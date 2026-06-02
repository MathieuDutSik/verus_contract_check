// CosmWasm linear-with-cliff vesting contract with a Verus-verified
// core. The schedule arithmetic, monotonicity-of-claimed property,
// and authorisation check live in `verified_helpers.rs` as
// `verified_instantiate` / `verified_claim` / `verified_vested`. The
// SDK-decorated `instantiate` / `execute` / `query` entry points below
// are thin forwarders that wrap CosmWasm's `&mut dyn Storage` in a
// `StoreRef` adapter and map the verified `ClaimError` onto a
// chain-specific `ContractError`.
//
// Layout (mirrors `linera_alternate` fungible):
//   - `pub mod core;`              — chain-agnostic verified core.
//   - `pub mod cw_axioms;`         — CosmWasm runtime axioms (storage
//                                    views + Addr/Uint128 type specs).
//   - `pub mod verified_helpers;`  — `verified_instantiate`,
//                                    `verified_claim`, `verified_vested`.
//   - this file                    — messages, error mapping, entry
//                                    points, tests.
//
// Build modes:
//   cargo build                                       — host build.
//   cargo test                                        — runs the unit tests.
//   cargo verus verify --target wasm32-unknown-unknown — verifies the core
//                                                       + verified helpers.

pub mod core;
pub mod cw_axioms;
pub mod verified_helpers;

use cosmwasm_schema::{cw_serde, QueryResponses};
use cosmwasm_std::{
    entry_point, to_json_binary, Addr, Binary, Deps, DepsMut, Env, MessageInfo, Response,
    StdError, StdResult, Storage, Uint128,
};
use thiserror::Error;

use crate::cw_axioms::{
    ax_has_beneficiary,
    BENEFICIARY, CLAIMED, CLIFF_DURATION, START, TOTAL, VEST_DURATION,
};
use crate::verified_helpers::{verified_claim, verified_instantiate, ClaimError};
use verus_vesting_core::{compute_claim, Params};

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
