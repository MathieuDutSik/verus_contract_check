// CosmWasm linear-with-cliff vesting contract with a Verus-verified
// core. The schedule arithmetic, monotonicity-of-claimed property,
// and authorisation check live inside the `verus!{}` block as
// `verified_claim` and `verified_instantiate`; the SDK-decorated
// `instantiate` / `execute` / `query` entry points are thin forwarders
// that wrap CosmWasm's `&mut dyn Storage` in our `StoreRef` adapter
// and map the verified `ClaimError` onto a chain-specific
// `ContractError`.
//
// Build modes:
//   cargo build                                       — host build.
//   cargo test                                        — runs the unit tests.
//   cargo verus verify --target wasm32-unknown-unknown — verifies the core
//                                                       + verified helpers.

pub mod core;
pub mod cw_axioms;

use cosmwasm_schema::{cw_serde, QueryResponses};
use cosmwasm_std::{
    entry_point, to_json_binary, Addr, Binary, Deps, DepsMut, Env, MessageInfo, Response,
    StdError, StdResult, Storage, Uint128,
};
use thiserror::Error;

use crate::cw_axioms::{
    ax_beneficiary_load, ax_beneficiary_save, ax_has_beneficiary,
    ax_claimed_load, ax_claimed_save,
    ax_cliff_load, ax_cliff_save,
    ax_start_load, ax_start_save,
    ax_total_load, ax_total_save,
    ax_vest_load, ax_vest_save,
    BENEFICIARY, CLAIMED, CLIFF_DURATION, START, TOTAL, VEST_DURATION,
};
use verus_vesting_core::{compute_claim, Params};

vstd::prelude::verus! {
    #[cfg(verus_only)]
    use vstd::prelude::*;
    #[cfg(verus_only)]
    use crate::core::{
        State, claimable_at, lemma_vested_bounded, state_after_claim,
    };
    #[cfg(verus_only)]
    use crate::cw_axioms::{
        beneficiary_view, claimed_view, cliff_view, start_view,
        total_view, vest_view,
    };

    /// Errors the verified helpers raise. Chain-specific error mapping
    /// (to `ContractError` below) happens in the entry-point glue.
    #[derive(PartialEq, Eq, Debug)]
    pub enum ClaimError {
        /// Caller isn't the registered beneficiary.
        Unauthorized,
        /// `compute_vested`'s arithmetic overflowed u128.
        ArithOverflow,
    }

    /// Spec-level summary: "all six storage views are populated AND
    /// the schedule is well-formed AND `claimed` is bounded by total".
    /// This is the invariant the contract maintains across instantiate
    /// and every subsequent claim. Used as a precondition on the
    /// verified helpers and as part of their postcondition.
    pub open spec fn vesting_ready<S: Storage>(s: &S) -> bool {
        &&& beneficiary_view(s).is_some()
        &&& start_view(s).is_some()
        &&& cliff_view(s).is_some()
        &&& vest_view(s).is_some()
        &&& total_view(s).is_some()
        &&& claimed_view(s).is_some()
        &&& (vest_view(s)->Some_0 > 0)
        &&& (cliff_view(s)->Some_0 <= vest_view(s)->Some_0)
        &&& (claimed_view(s)->Some_0 <= total_view(s)->Some_0)
    }

    /// Construct the `Params` view from the (assumed-populated) views.
    /// Used in the state-level ensures of `verified_claim`.
    pub open spec fn params_of<S: Storage>(s: &S) -> Params {
        Params {
            start:          start_view(s)->Some_0,
            cliff_duration: cliff_view(s)->Some_0,
            vest_duration:  vest_view(s)->Some_0,
            total:          total_view(s)->Some_0,
        }
    }

    /// Verified `instantiate`: persist the full bundle. The entry
    /// point checks `vest_duration > 0` and `cliff_duration <=
    /// vest_duration` (we *require* them) and validates the
    /// beneficiary string before calling in.
    ///
    /// Post: every view is `Some(<initial>)` and the invariant holds.
    pub fn verified_instantiate<S: Storage>(
        storage:        &mut S,
        beneficiary:    Addr,
        start_ms:       u64,
        cliff_duration: u64,
        vest_duration:  u64,
        total:          u128,
    )
        requires
            vest_duration > 0,
            cliff_duration <= vest_duration,
        ensures
            beneficiary_view(final(storage)) == Some(beneficiary),
            start_view(final(storage))       == Some(start_ms),
            cliff_view(final(storage))       == Some(cliff_duration),
            vest_view(final(storage))        == Some(vest_duration),
            total_view(final(storage))       == Some(total),
            claimed_view(final(storage))     == Some(0u128),
            vesting_ready(final(storage)),
    {
        ax_beneficiary_save(storage, &beneficiary);
        ax_start_save(storage, start_ms);
        ax_cliff_save(storage, cliff_duration);
        ax_vest_save(storage, vest_duration);
        ax_total_save(storage, total);
        ax_claimed_save(storage, 0);
    }

    /// Verified `claim`: release everything currently claimable to the
    /// beneficiary, gated on the caller matching the registered one.
    ///
    /// Returns the amount released this call.
    ///
    /// `ensures` (success path):
    ///
    ///   - authorisation: caller == registered beneficiary.
    ///   - state-level connection: post `claimed` is exactly
    ///     `state_after_claim(pre_state, now_ms).claimed`, where
    ///     `pre_state` is the spec-level `State<Addr>` reconstructed
    ///     from the storage views.
    ///   - monotonicity: post.claimed >= pre.claimed.
    ///   - returned amount equals the delta in claimed.
    ///   - the five immutable views (beneficiary, start, cliff, vest,
    ///     total) are preserved verbatim.
    ///   - the invariant `vesting_ready` is preserved.
    pub fn verified_claim<S: Storage>(
        storage:  &mut S,
        sender:   &Addr,
        now_ms:   u64,
    ) -> (r: Result<u128, ClaimError>)
        requires vesting_ready(old(storage)),
        ensures
            // Invariant always preserved.
            vesting_ready(final(storage)),
            // Five immutable views never change.
            beneficiary_view(final(storage)) == beneficiary_view(old(storage)),
            start_view(final(storage))       == start_view(old(storage)),
            cliff_view(final(storage))       == cliff_view(old(storage)),
            vest_view(final(storage))        == vest_view(old(storage)),
            total_view(final(storage))       == total_view(old(storage)),
            // claimed is monotone.
            claimed_view(final(storage))->Some_0 >= claimed_view(old(storage))->Some_0,
            // Result-specific.
            match r {
                Ok(amount) => {
                    let pre  = claimed_view(old(storage))->Some_0;
                    let post = claimed_view(final(storage))->Some_0;
                    &&& *sender == beneficiary_view(old(storage))->Some_0
                    &&& amount as int == (post as int) - (pre as int)
                    // State-level connection: post == state_after_claim
                    &&& post as int
                        == state_after_claim::<Addr>(
                                State {
                                    beneficiary: beneficiary_view(old(storage))->Some_0,
                                    params:      params_of(old(storage)),
                                    claimed:     pre,
                                },
                                now_ms,
                           ).claimed as int
                }
                Err(_) => true,
            },
    {
        // 1. Authorization. UFCS form `<Addr as PartialEq>::eq(...)`
        //    routes to the spec'd `assume_specification` in cw_axioms;
        //    the surface form `sender == &beneficiary` would resolve
        //    to the blanket `<&Addr as PartialEq<&Addr>>::eq` and
        //    Verus has no spec for that.
        let beneficiary = ax_beneficiary_load(storage);
        if !<Addr as ::core::cmp::PartialEq>::eq(sender, &beneficiary) {
            return Err(ClaimError::Unauthorized);
        }

        // 2. Read the immutable schedule + the mutable claimed.
        let start          = ax_start_load(storage);
        let cliff_duration = ax_cliff_load(storage);
        let vest_duration  = ax_vest_load(storage);
        let total          = ax_total_load(storage);
        let claimed_pre    = ax_claimed_load(storage);

        let params = Params { start, cliff_duration, vest_duration, total };

        // 3. Schedule lookup.
        let amount = match compute_claim(&params, now_ms, claimed_pre) {
            Ok(a)  => a,
            Err(_) => return Err(ClaimError::ArithOverflow),
        };

        // 4. Bound the addition for the no-overflow check. The bounded
        //    lemma gives `vested_at(p, now_ms) <= total`; chained with
        //    `compute_claim`'s post this caps `claimed_pre + amount`
        //    at `total`.
        proof {
            lemma_vested_bounded(params, now_ms);
        }

        // 5. Write back the new claimed (only if it changed, to skip
        //    the no-op storage write).
        if amount > 0 {
            ax_claimed_save(storage, claimed_pre + amount);
        }
        Ok(amount)
    }

    /// Verified view: how much *would* be vested at `now_ms`, ignoring
    /// the already-claimed amount.
    pub fn verified_vested<S: Storage>(
        storage: &S,
        now_ms:  u64,
    ) -> (r: Result<u128, ClaimError>)
        requires vesting_ready(storage),
    {
        let start          = ax_start_load(storage);
        let cliff_duration = ax_cliff_load(storage);
        let vest_duration  = ax_vest_load(storage);
        let total          = ax_total_load(storage);
        let params = Params { start, cliff_duration, vest_duration, total };
        match verus_vesting_core::compute_vested(&params, now_ms) {
            Ok(v)  => Ok(v),
            Err(_) => Err(ClaimError::ArithOverflow),
        }
    }
}

// =====================================================================
// CosmWasm SDK glue (unverified): messages, entry points, error
// mapping, and the `StoreRef` adapter that gives the verified helpers
// (which require `S: Sized`) a concrete view of `&mut dyn Storage`.
// =====================================================================

#[cw_serde]
pub struct InstantiateMsg {
    pub beneficiary:       String,
    pub start_ms:          u64,
    pub cliff_duration_ms: u64,
    pub vest_duration_ms:  u64,
    pub total:             Uint128,
}

#[cw_serde]
pub enum ExecuteMsg {
    Claim {},
}

#[cw_serde]
#[derive(QueryResponses)]
pub enum QueryMsg {
    #[returns(Addr)]    Beneficiary {},
    #[returns(Uint128)] Total {},
    #[returns(Uint128)] Claimed {},
    #[returns(Uint128)] VestedNow {},
    #[returns(Uint128)] ClaimableNow {},
}

#[derive(Error, Debug)]
pub enum ContractError {
    #[error("{0}")]                                       Std(#[from] StdError),
    #[error("unauthorized")]                              Unauthorized,
    #[error("vest_duration must be > 0")]                 ZeroVestDuration,
    #[error("cliff_duration must be <= vest_duration")]   CliffTooLong,
    #[error("schedule arithmetic overflow")]              ArithOverflow,
    #[error("not instantiated")]                          NotInstantiated,
    #[error("already instantiated")]                      AlreadyInstantiated,
}

fn map_claim_error(e: ClaimError) -> ContractError {
    match e {
        ClaimError::Unauthorized  => ContractError::Unauthorized,
        ClaimError::ArithOverflow => ContractError::ArithOverflow,
    }
}

/// Concrete wrapper around `&mut dyn Storage` so the verified helpers
/// (which take `<S: Storage>` and need `S: Sized`) can operate on
/// `DepsMut.storage`. Same shape as the fungible contract's `StoreRef`.
pub struct StoreRef<'a>(pub &'a mut dyn Storage);

impl Storage for StoreRef<'_> {
    fn get(&self, key: &[u8]) -> Option<Vec<u8>> { self.0.get(key) }
    fn set(&mut self, key: &[u8], value: &[u8]) { self.0.set(key, value) }
    fn remove(&mut self, key: &[u8]) { self.0.remove(key) }
}

/// Read-only counterpart for queries.
pub struct StoreRefRead<'a>(pub &'a dyn Storage);

impl Storage for StoreRefRead<'_> {
    fn get(&self, key: &[u8]) -> Option<Vec<u8>> { self.0.get(key) }
    fn set(&mut self, _key: &[u8], _value: &[u8]) {
        unreachable!("StoreRefRead is read-only");
    }
    fn remove(&mut self, _key: &[u8]) {
        unreachable!("StoreRefRead is read-only");
    }
}

#[entry_point]
pub fn instantiate(
    deps: DepsMut,
    _env: Env,
    _info: MessageInfo,
    msg: InstantiateMsg,
) -> Result<Response, ContractError> {
    if msg.vest_duration_ms == 0 {
        return Err(ContractError::ZeroVestDuration);
    }
    if msg.cliff_duration_ms > msg.vest_duration_ms {
        return Err(ContractError::CliffTooLong);
    }
    let beneficiary = deps.api.addr_validate(&msg.beneficiary)?;
    let mut store_ref = StoreRef(deps.storage);
    if ax_has_beneficiary(&store_ref) {
        return Err(ContractError::AlreadyInstantiated);
    }
    verified_instantiate(
        &mut store_ref,
        beneficiary.clone(),
        msg.start_ms,
        msg.cliff_duration_ms,
        msg.vest_duration_ms,
        msg.total.u128(),
    );
    Ok(Response::new()
        .add_attribute("action", "instantiate")
        .add_attribute("beneficiary", beneficiary)
        .add_attribute("total", msg.total.to_string()))
}

#[entry_point]
pub fn execute(
    deps: DepsMut,
    env:  Env,
    info: MessageInfo,
    msg:  ExecuteMsg,
) -> Result<Response, ContractError> {
    let mut store_ref = StoreRef(deps.storage);
    match msg {
        ExecuteMsg::Claim {} => {
            if !ax_has_beneficiary(&store_ref) {
                return Err(ContractError::NotInstantiated);
            }
            // The `vesting_ready` invariant is implicitly maintained
            // by the contract: instantiate establishes it, and the
            // verified helper preserves it. The entry-point glue is
            // unverified, so we assert one cheap consequence — the
            // beneficiary view is populated — and trust the rest.
            let now_ms = env.block.time.nanos() / 1_000_000;
            let amount = verified_claim(&mut store_ref, &info.sender, now_ms)
                .map_err(map_claim_error)?;
            Ok(Response::new()
                .add_attribute("action", "claim")
                .add_attribute("beneficiary", info.sender)
                .add_attribute("amount", amount.to_string()))
        }
    }
}

#[entry_point]
pub fn query(deps: Deps, env: Env, msg: QueryMsg) -> StdResult<Binary> {
    match msg {
        QueryMsg::Beneficiary {} => to_json_binary(
            &BENEFICIARY.may_load(deps.storage)?
                .ok_or_else(|| StdError::generic_err("not instantiated"))?,
        ),
        QueryMsg::Total {} => to_json_binary(
            &TOTAL.may_load(deps.storage)?
                .ok_or_else(|| StdError::generic_err("not instantiated"))?,
        ),
        QueryMsg::Claimed {} => to_json_binary(
            &CLAIMED.may_load(deps.storage)?
                .ok_or_else(|| StdError::generic_err("not instantiated"))?,
        ),
        QueryMsg::VestedNow {} => {
            let start = START.may_load(deps.storage)?
                .ok_or_else(|| StdError::generic_err("not instantiated"))?;
            let cliff_duration = CLIFF_DURATION.load(deps.storage)?;
            let vest_duration  = VEST_DURATION.load(deps.storage)?;
            let total          = TOTAL.load(deps.storage)?.u128();
            let params = Params { start, cliff_duration, vest_duration, total };
            let now_ms = env.block.time.nanos() / 1_000_000;
            match verus_vesting_core::compute_vested(&params, now_ms) {
                Ok(v)  => to_json_binary(&Uint128::new(v)),
                Err(_) => Err(StdError::generic_err("schedule arithmetic overflow")),
            }
        }
        QueryMsg::ClaimableNow {} => {
            let start = START.may_load(deps.storage)?
                .ok_or_else(|| StdError::generic_err("not instantiated"))?;
            let cliff_duration = CLIFF_DURATION.load(deps.storage)?;
            let vest_duration  = VEST_DURATION.load(deps.storage)?;
            let total          = TOTAL.load(deps.storage)?.u128();
            let claimed        = CLAIMED.load(deps.storage)?.u128();
            let params = Params { start, cliff_duration, vest_duration, total };
            let now_ms = env.block.time.nanos() / 1_000_000;
            match compute_claim(&params, now_ms, claimed) {
                Ok(a)  => to_json_binary(&Uint128::new(a)),
                Err(_) => Err(StdError::generic_err("schedule arithmetic overflow")),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use cosmwasm_std::testing::{message_info, mock_dependencies, mock_env, MockApi, MockQuerier, MockStorage};
    use cosmwasm_std::{from_json, Addr, OwnedDeps, Timestamp};

    struct Actors { admin: Addr, ben: Addr, attacker: Addr }
    fn actors(api: &MockApi) -> Actors {
        Actors {
            admin:    api.addr_make("admin"),
            ben:      api.addr_make("ben"),
            attacker: api.addr_make("attacker"),
        }
    }

    fn env_at(now_ms: u64) -> Env {
        let mut e = mock_env();
        e.block.time = Timestamp::from_nanos(now_ms.saturating_mul(1_000_000));
        e
    }

    fn setup() -> (OwnedDeps<MockStorage, MockApi, MockQuerier>, Actors) {
        let mut deps = mock_dependencies();
        let a = actors(&deps.api);
        let info = message_info(&a.admin, &[]);
        let msg = InstantiateMsg {
            beneficiary:       a.ben.to_string(),
            start_ms:          1_000,
            cliff_duration_ms: 500,
            vest_duration_ms:  2_000,
            total:             Uint128::new(1_000_000),
        };
        instantiate(deps.as_mut(), env_at(0), info, msg).unwrap();
        (deps, a)
    }

    fn query_u128(deps: Deps, env: Env, msg: QueryMsg) -> u128 {
        let bin = query(deps, env, msg).unwrap();
        let v: Uint128 = from_json(&bin).unwrap();
        v.u128()
    }

    fn claim(
        deps: &mut OwnedDeps<MockStorage, MockApi, MockQuerier>,
        caller: &Addr,
        now_ms: u64,
    ) -> Result<u128, ContractError> {
        let info = message_info(caller, &[]);
        let resp = execute(deps.as_mut(), env_at(now_ms), info, ExecuteMsg::Claim {})?;
        let amt = resp.attributes.iter()
            .find(|a| a.key == "amount")
            .unwrap()
            .value.parse::<u128>().unwrap();
        Ok(amt)
    }

    #[test]
    fn init_state_persists() {
        let (deps, a) = setup();
        assert_eq!(query_u128(deps.as_ref(), env_at(0), QueryMsg::Total {}), 1_000_000);
        assert_eq!(query_u128(deps.as_ref(), env_at(0), QueryMsg::Claimed {}), 0);
        let bin = query(deps.as_ref(), env_at(0), QueryMsg::Beneficiary {}).unwrap();
        let b: Addr = from_json(&bin).unwrap();
        assert_eq!(b, a.ben);
    }

    #[test]
    fn init_rejects_zero_vest_duration() {
        let mut deps = mock_dependencies();
        let a = actors(&deps.api);
        let msg = InstantiateMsg {
            beneficiary: a.ben.to_string(),
            start_ms: 0, cliff_duration_ms: 0, vest_duration_ms: 0,
            total: Uint128::new(1_000),
        };
        let err = instantiate(deps.as_mut(), env_at(0), message_info(&a.admin, &[]), msg).unwrap_err();
        assert!(matches!(err, ContractError::ZeroVestDuration));
    }

    #[test]
    fn init_rejects_cliff_longer_than_vest() {
        let mut deps = mock_dependencies();
        let a = actors(&deps.api);
        let msg = InstantiateMsg {
            beneficiary: a.ben.to_string(),
            start_ms: 0, cliff_duration_ms: 5_000, vest_duration_ms: 1_000,
            total: Uint128::new(1_000),
        };
        let err = instantiate(deps.as_mut(), env_at(0), message_info(&a.admin, &[]), msg).unwrap_err();
        assert!(matches!(err, ContractError::CliffTooLong));
    }

    #[test]
    fn init_twice_rejected() {
        let (mut deps, a) = setup();
        let msg = InstantiateMsg {
            beneficiary: a.ben.to_string(),
            start_ms: 0, cliff_duration_ms: 0, vest_duration_ms: 1_000,
            total: Uint128::new(1_000),
        };
        let err = instantiate(deps.as_mut(), env_at(0), message_info(&a.admin, &[]), msg).unwrap_err();
        assert!(matches!(err, ContractError::AlreadyInstantiated));
    }

    #[test]
    fn pre_cliff_nothing_vested() {
        let (deps, _) = setup();
        assert_eq!(query_u128(deps.as_ref(), env_at(1_499), QueryMsg::VestedNow {}), 0);
        assert_eq!(query_u128(deps.as_ref(), env_at(1_499), QueryMsg::ClaimableNow {}), 0);
    }

    #[test]
    fn pre_start_nothing_vested() {
        let (deps, _) = setup();
        assert_eq!(query_u128(deps.as_ref(), env_at(500), QueryMsg::VestedNow {}), 0);
    }

    #[test]
    fn at_cliff_proportional() {
        let (deps, _) = setup();
        assert_eq!(query_u128(deps.as_ref(), env_at(1_500), QueryMsg::VestedNow {}), 250_000);
        assert_eq!(query_u128(deps.as_ref(), env_at(1_500), QueryMsg::ClaimableNow {}), 250_000);
    }

    #[test]
    fn mid_vest_linear() {
        let (deps, _) = setup();
        assert_eq!(query_u128(deps.as_ref(), env_at(2_000), QueryMsg::VestedNow {}), 500_000);
    }

    #[test]
    fn end_of_vest_full() {
        let (deps, _) = setup();
        assert_eq!(query_u128(deps.as_ref(), env_at(3_000), QueryMsg::VestedNow {}), 1_000_000);
    }

    #[test]
    fn post_end_caps_at_total() {
        let (deps, _) = setup();
        assert_eq!(query_u128(deps.as_ref(), env_at(1_000_000_000_000), QueryMsg::VestedNow {}), 1_000_000);
    }

    #[test]
    fn claim_at_cliff_returns_quarter() {
        let (mut deps, a) = setup();
        let released = claim(&mut deps, &a.ben, 1_500).unwrap();
        assert_eq!(released, 250_000);
        assert_eq!(query_u128(deps.as_ref(), env_at(1_500), QueryMsg::Claimed {}), 250_000);
        let again = claim(&mut deps, &a.ben, 1_500).unwrap();
        assert_eq!(again, 0);
        assert_eq!(query_u128(deps.as_ref(), env_at(1_500), QueryMsg::Claimed {}), 250_000);
    }

    #[test]
    fn claim_pre_cliff_returns_zero() {
        let (mut deps, a) = setup();
        let released = claim(&mut deps, &a.ben, 1_000).unwrap();
        assert_eq!(released, 0);
        assert_eq!(query_u128(deps.as_ref(), env_at(1_000), QueryMsg::Claimed {}), 0);
    }

    #[test]
    fn claim_monotonic_across_two_blocks() {
        let (mut deps, a) = setup();
        let r1 = claim(&mut deps, &a.ben, 2_000).unwrap();
        assert_eq!(r1, 500_000);
        let r2 = claim(&mut deps, &a.ben, 3_000).unwrap();
        assert_eq!(r2, 500_000);
        assert_eq!(r1 + r2, query_u128(deps.as_ref(), env_at(3_000), QueryMsg::Total {}));
    }

    #[test]
    fn claim_post_end_drains() {
        let (mut deps, a) = setup();
        let released = claim(&mut deps, &a.ben, 10_000).unwrap();
        assert_eq!(released, 1_000_000);
        let again = claim(&mut deps, &a.ben, 10_000).unwrap();
        assert_eq!(again, 0);
    }

    #[test]
    fn claim_unauthorized_rejected() {
        let (mut deps, a) = setup();
        let err = claim(&mut deps, &a.attacker, 2_000).unwrap_err();
        assert!(matches!(err, ContractError::Unauthorized));
        assert_eq!(query_u128(deps.as_ref(), env_at(2_000), QueryMsg::Claimed {}), 0);
    }
}
