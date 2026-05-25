pub mod core;
pub mod cw_axioms;

use cosmwasm_schema::{cw_serde, QueryResponses};
use cosmwasm_std::{
    entry_point, to_json_binary, Addr, Binary, Deps, DepsMut, Env, MessageInfo, Response,
    StdError, StdResult, Storage, Uint128,
};
use thiserror::Error;

// Storage handles live in cw_axioms.rs so the runtime calls and the
// axiomatized helpers share a single set of `Map`/`Item` definitions.
use crate::cw_axioms::{
    TOTAL_SUPPLY,
    ax_balances_load, ax_balances_save, ax_supply_load, ax_supply_save,
    ax_allowances_load, ax_allowances_save,
};

// -- Verified transfer helper ------------------------------------------
//
// Single function that captures every substantive step of the contract's
// `Transfer` execute branch: caller/recipient comparison, balance reads,
// arithmetic via the verified `core::transfer_balances`, balance writes.
// The `ensures` clause pins down the storage effect on the abstract
// `balances_view` of `Storage`, using the axioms in `cw_axioms.rs`.

vstd::prelude::verus! {
    #[cfg(verus_only)]
    use vstd::prelude::*;
    #[cfg(verus_only)]
    use vstd::map::Map as SpecMap;
    #[cfg(verus_only)]
    use crate::cw_axioms::{balances_view, supply_view, allowances_view};

    /// Failure modes of `verified_transfer` / `verified_transfer_from`.
    /// Mirrors the runtime `ContractError` but is closed (no `Std`
    /// variant) so it can be returned from verified code.
    #[derive(PartialEq, Eq)]
    pub enum TransferError {
        SelfTransfer,
        Insufficient,
        Overflow,
        InsufficientAllowance,
    }

    /// Balance of `k` in the abstract map, with absent entries treated as 0.
    pub open spec fn balance_at(m: SpecMap<Addr, u128>, k: Addr) -> u128 {
        if m.dom().contains(k) { m[k] } else { 0u128 }
    }

    /// The map after `state_after_transfer`'s balance update.
    pub open spec fn transfer_balances_map(
        m: SpecMap<Addr, u128>,
        sender: Addr,
        receiver: Addr,
        amount: u128,
    ) -> SpecMap<Addr, u128> {
        m.insert(sender,   (balance_at(m, sender) - amount) as u128)
         .insert(receiver, (balance_at(m, receiver) + amount) as u128)
    }

    /// Verified transfer step: ensures the storage update matches
    /// `transfer_balances_map` on success, leaves storage untouched on
    /// error. `supply_view` and `allowances_view` are preserved either
    /// way (transfers only touch balances).
    pub fn verified_transfer<S: Storage>(
        storage:  &mut S,
        sender:   &Addr,
        receiver: &Addr,
        amount:   u128,
    ) -> (r: Result<(), TransferError>)
        ensures
            match r {
                Ok(()) =>
                    *sender != *receiver
                    && balances_view(final(storage))
                        == transfer_balances_map(balances_view(old(storage)), *sender, *receiver, amount)
                    && supply_view(final(storage))     == supply_view(old(storage))
                    && allowances_view(final(storage)) == allowances_view(old(storage)),
                Err(_) => true,
            },
    {
        if *sender == *receiver {
            return Err(TransferError::SelfTransfer);
        }
        let from = ax_balances_load(storage, sender);
        let to   = ax_balances_load(storage, receiver);
        proof {
            // Pin balances_view(old(storage)) as `pre` so subsequent
            // asserts have a single name to reason about.
            assert(from == balance_at(balances_view(old(storage)), *sender));
            assert(to   == balance_at(balances_view(old(storage)), *receiver));
        }
        match crate::core::transfer_balances(from, to, amount) {
            Ok((from_next, to_next)) => {
                ax_balances_save(storage, sender, from_next);
                // After the first save, the receiver's balance is
                // unchanged (sender != receiver, and insert at sender
                // doesn't touch other keys).
                proof {
                    assert(balance_at(balances_view(storage), *receiver) == to);
                }
                ax_balances_save(storage, receiver, to_next);
                Ok(())
            }
            Err(_msg) => {
                if from < amount { Err(TransferError::Insufficient) }
                else             { Err(TransferError::Overflow) }
            }
        }
    }

    // ---- Connection to `core::State` ----------------------------------
    //
    // `verified_transfer` operates on `u128` storage. `core::State<A>`
    // and `core::state_after_transfer` operate on `nat` (for unbounded
    // arithmetic in proofs). The bridge is `nat_balances`, lifting
    // `u128`-valued maps to `nat`-valued maps point-wise.

    /// Lift a `u128`-valued balance map into the `nat`-valued spec map.
    pub open spec fn nat_balances(m: SpecMap<Addr, u128>) -> SpecMap<Addr, nat> {
        SpecMap::new(
            |a: Addr| m.dom().contains(a),
            |a: Addr| m[a] as nat,
        )
    }

    /// Verified instantiate step: sets `TOTAL_SUPPLY` to `total_supply`
    /// and credits the owner with the full supply. The `ensures` captures
    /// the storage delta — the view changes by exactly one balance insert
    /// at `owner`, and the supply is set.
    ///
    /// Together with the assumption that the initial `balances_view` is
    /// empty (which the cosmwasm runtime guarantees at deployment but we
    /// don't formalise here), this establishes `sum(balances) ==
    /// total_supply` post-instantiate — the conservation invariant.
    pub fn verified_instantiate<S: Storage>(
        storage: &mut S,
        owner:   &Addr,
        total_supply: u128,
    )
        ensures
            supply_view(final(storage)) == total_supply,
            balances_view(final(storage))
                == balances_view(old(storage)).insert(*owner, total_supply),
    {
        ax_supply_save(storage, total_supply);
        ax_balances_save(storage, owner, total_supply);
    }

    /// Verified balance lookup: returns the owner's balance per the abstract
    /// view, defaulting absent entries to 0.
    pub fn verified_balance_of<S: Storage>(
        storage: &S,
        account: &Addr,
    ) -> (r: u128)
        ensures
            r == balance_at(balances_view(storage), *account),
    {
        ax_balances_load(storage, account)
    }

    // -- cw20 allowance machinery --------------------------------------

    /// Allowance for `(owner, spender)` in the abstract map, defaulting
    /// absent entries to 0.
    pub open spec fn allowance_at(
        m: SpecMap<(Addr, Addr), u128>,
        owner: Addr,
        spender: Addr,
    ) -> u128 {
        if m.dom().contains((owner, spender)) { m[(owner, spender)] } else { 0u128 }
    }

    /// Verified allowance query: returns the `(owner, spender)` allowance
    /// per the abstract view.
    pub fn verified_allowance<S: Storage>(
        storage: &S,
        owner:   &Addr,
        spender: &Addr,
    ) -> (r: u128)
        ensures
            r == allowance_at(allowances_view(storage), *owner, *spender),
    {
        ax_allowances_load(storage, owner, spender)
    }

    /// Verified `approve`: `owner` sets `spender`'s allowance to exactly
    /// `amount`, replacing any previous value. Balances and supply are
    /// untouched.
    pub fn verified_approve<S: Storage>(
        storage: &mut S,
        owner:   &Addr,
        spender: &Addr,
        amount:  u128,
    )
        ensures
            allowances_view(final(storage))
                == allowances_view(old(storage)).insert((*owner, *spender), amount),
            balances_view(final(storage)) == balances_view(old(storage)),
            supply_view(final(storage))   == supply_view(old(storage)),
    {
        ax_allowances_save(storage, owner, spender, amount);
    }

    /// Verified `transfer_from`: `spender` moves `amount` from `owner` to
    /// `recipient`, decrementing the `(owner, spender)` allowance by the
    /// same amount. Fails (without state change) if:
    ///   - owner == recipient (self-transfer)
    ///   - allowance is below `amount` (InsufficientAllowance)
    ///   - owner's balance is below `amount` (Insufficient)
    ///   - recipient's balance + `amount` overflows u128 (Overflow)
    pub fn verified_transfer_from<S: Storage>(
        storage:   &mut S,
        spender:   &Addr,
        owner:     &Addr,
        recipient: &Addr,
        amount:    u128,
    ) -> (r: Result<(), TransferError>)
        ensures
            match r {
                Ok(()) =>
                    *owner != *recipient
                    && balances_view(final(storage))
                        == transfer_balances_map(balances_view(old(storage)), *owner, *recipient, amount)
                    && supply_view(final(storage)) == supply_view(old(storage))
                    && allowances_view(final(storage))
                        == allowances_view(old(storage)).insert(
                            (*owner, *spender),
                            (allowance_at(allowances_view(old(storage)), *owner, *spender) - amount) as u128
                        ),
                Err(_) => true,
            },
    {
        // Allowance check first (cheap, no state change on failure).
        let current_allowance = ax_allowances_load(storage, owner, spender);
        if current_allowance < amount {
            return Err(TransferError::InsufficientAllowance);
        }
        // Do the transfer; on failure, allowance is unchanged.
        match verified_transfer(storage, owner, recipient, amount) {
            Ok(()) => {
                // Transfer succeeded — decrement the allowance.
                // We pass `current_allowance` (read before the transfer)
                // because `ax_balances_save` preserves allowances_view,
                // so the value is still current.
                ax_allowances_save(storage, owner, spender, current_allowance - amount);
                Ok(())
            }
            Err(e) => Err(e),
        }
    }

    /// Refinement: the `u128`-level transfer (`transfer_balances_map`)
    /// matches the `nat`-level transfer (`core::state_after_transfer`'s
    /// `.balances`) when viewed through `nat_balances`, provided the
    /// arithmetic doesn't under/overflow.
    pub proof fn lemma_verified_transfer_matches_state(
        balances_pre: SpecMap<Addr, u128>,
        sender:       Addr,
        receiver:     Addr,
        amount:       u128,
    )
        requires
            sender != receiver,
            balances_pre.dom().contains(sender),
            balances_pre.dom().contains(receiver),
            balances_pre[sender] >= amount,
            balances_pre[receiver] as int + amount as int <= u128::MAX as int,
        ensures
            nat_balances(transfer_balances_map(balances_pre, sender, receiver, amount))
                == crate::core::state_after_transfer(
                    crate::core::State {
                        total_supply: 0nat,
                        balances:     nat_balances(balances_pre),
                    },
                    sender, receiver, amount as nat,
                ).balances,
    {
        let bp  = balances_pre;
        let f   = bp[sender];
        let t   = bp[receiver];
        let lhs = nat_balances(
            bp.insert(sender,   (f - amount) as u128)
              .insert(receiver, (t + amount) as u128)
        );
        let rhs = crate::core::state_after_transfer(
            crate::core::State {
                total_supply: 0nat,
                balances:     nat_balances(bp),
            },
            sender, receiver, amount as nat,
        ).balances;

        assert(lhs.dom() =~= rhs.dom());

        assert forall|k: Addr| #[trigger] lhs.dom().contains(k)
            implies lhs[k] == rhs[k]
        by {
            if k == sender {
                // (f - amount) as u128 as nat == (f as nat - amount as nat) as nat
            } else if k == receiver {
                // (t + amount) as u128 as nat == (t as nat + amount as nat) as nat
            } else {
                assert(bp.dom().contains(k));
            }
        }
        assert(lhs =~= rhs);
    }

    // -- Mint & burn ----------------------------------------------------

    /// Verified `mint`: credits `amount` to `to` and increases
    /// `total_supply` by the same amount. Fails on supply overflow.
    /// No authorization check — wrapping callers should enforce that
    /// (typically restricted to a Minter address in real cw20).
    pub fn verified_mint<S: Storage>(
        storage: &mut S,
        to:      &Addr,
        amount:  u128,
    ) -> (r: Result<(), TransferError>)
        ensures
            match r {
                Ok(()) =>
                    supply_view(final(storage))
                        == (supply_view(old(storage)) + amount) as u128
                    && balances_view(final(storage))
                        == balances_view(old(storage)).insert(
                            *to,
                            (balance_at(balances_view(old(storage)), *to) + amount) as u128,
                        )
                    && allowances_view(final(storage)) == allowances_view(old(storage)),
                Err(_) => true,
            },
    {
        let supply = ax_supply_load(storage);
        let bal    = ax_balances_load(storage, to);
        // Both arithmetic operations must succeed.
        let new_supply = match supply.checked_add(amount) {
            Some(v) => v,
            None    => return Err(TransferError::Overflow),
        };
        let new_bal = match bal.checked_add(amount) {
            Some(v) => v,
            None    => return Err(TransferError::Overflow),
        };
        ax_supply_save(storage, new_supply);
        ax_balances_save(storage, to, new_bal);
        Ok(())
    }

    /// Verified `burn`: debits `amount` from `from` and decreases
    /// `total_supply` by the same amount. Fails if `from` doesn't have
    /// enough balance. The caller is expected to be `from` in cw20
    /// (you burn your own tokens); we don't enforce that here.
    pub fn verified_burn<S: Storage>(
        storage: &mut S,
        from:    &Addr,
        amount:  u128,
    ) -> (r: Result<(), TransferError>)
        ensures
            match r {
                Ok(()) =>
                    supply_view(final(storage))
                        == (supply_view(old(storage)) - amount) as u128
                    && balances_view(final(storage))
                        == balances_view(old(storage)).insert(
                            *from,
                            (balance_at(balances_view(old(storage)), *from) - amount) as u128,
                        )
                    && allowances_view(final(storage)) == allowances_view(old(storage)),
                Err(_) => true,
            },
    {
        let supply = ax_supply_load(storage);
        let bal    = ax_balances_load(storage, from);
        let new_bal = match bal.checked_sub(amount) {
            Some(v) => v,
            None    => return Err(TransferError::Insufficient),
        };
        let new_supply = match supply.checked_sub(amount) {
            Some(v) => v,
            None    => return Err(TransferError::Insufficient),
        };
        ax_supply_save(storage, new_supply);
        ax_balances_save(storage, from, new_bal);
        Ok(())
    }

    // -- Allowance delta operations ------------------------------------

    /// Atomic increase of `(owner, spender)` allowance by `amount`.
    /// Fails on overflow. No state change on failure.
    pub fn verified_increase_allowance<S: Storage>(
        storage: &mut S,
        owner:   &Addr,
        spender: &Addr,
        amount:  u128,
    ) -> (r: Result<(), TransferError>)
        ensures
            match r {
                Ok(()) =>
                    allowances_view(final(storage))
                        == allowances_view(old(storage)).insert(
                            (*owner, *spender),
                            (allowance_at(allowances_view(old(storage)), *owner, *spender) + amount) as u128,
                        )
                    && balances_view(final(storage)) == balances_view(old(storage))
                    && supply_view(final(storage))   == supply_view(old(storage)),
                Err(_) => true,
            },
    {
        let current = ax_allowances_load(storage, owner, spender);
        match current.checked_add(amount) {
            Some(new) => {
                ax_allowances_save(storage, owner, spender, new);
                Ok(())
            }
            None => Err(TransferError::Overflow),
        }
    }

    /// Atomic decrease of `(owner, spender)` allowance by `amount`,
    /// saturating at 0 (cw20 convention). Always succeeds.
    pub fn verified_decrease_allowance<S: Storage>(
        storage: &mut S,
        owner:   &Addr,
        spender: &Addr,
        amount:  u128,
    )
        ensures
            allowances_view(final(storage))
                == allowances_view(old(storage)).insert(
                    (*owner, *spender),
                    if allowance_at(allowances_view(old(storage)), *owner, *spender) >= amount {
                        (allowance_at(allowances_view(old(storage)), *owner, *spender) - amount) as u128
                    } else {
                        0u128
                    },
                ),
            balances_view(final(storage)) == balances_view(old(storage)),
            supply_view(final(storage))   == supply_view(old(storage)),
    {
        let current = ax_allowances_load(storage, owner, spender);
        let new = if current >= amount { current - amount } else { 0u128 };
        ax_allowances_save(storage, owner, spender, new);
    }
}

#[cw_serde]
pub struct InstantiateMsg {
    pub total_supply: Uint128,
}

#[cw_serde]
pub enum ExecuteMsg {
    Transfer          { recipient: String, amount: Uint128 },
    Approve           { spender:   String, amount: Uint128 },
    TransferFrom      { owner:     String, recipient: String, amount: Uint128 },
    Mint              { recipient: String, amount: Uint128 },
    Burn              { amount: Uint128 },
    IncreaseAllowance { spender:   String, amount: Uint128 },
    DecreaseAllowance { spender:   String, amount: Uint128 },
}

#[cw_serde]
#[derive(QueryResponses)]
pub enum QueryMsg {
    #[returns(Uint128)] BalanceOf   { account: String },
    #[returns(Uint128)] TotalSupply {},
    #[returns(Uint128)] Allowance   { owner: String, spender: String },
}

#[derive(Error, Debug)]
pub enum ContractError {
    #[error("{0}")]                       Std(#[from] StdError),
    #[error("insufficient balance")]      Insufficient,
    #[error("overflow")]                  Overflow,
    #[error("self-transfer")]             SelfTransfer,
    #[error("insufficient allowance")]    InsufficientAllowance,
}

/// Concrete wrapper around `&mut dyn Storage` so we can call the
/// verified helpers (which require `S: Sized`). `Storage` is impl'd by
/// delegation to the inner reference.
pub struct StoreRef<'a>(pub &'a mut dyn Storage);

impl Storage for StoreRef<'_> {
    fn get(&self, key: &[u8]) -> Option<Vec<u8>> { self.0.get(key) }
    fn set(&mut self, key: &[u8], value: &[u8]) { self.0.set(key, value) }
    fn remove(&mut self, key: &[u8]) { self.0.remove(key) }
}

/// Read-only counterpart of `StoreRef`. `Storage` requires `set` and
/// `remove` even on `&mut self`, so these panic — the wrapper is meant
/// to be used only in query contexts where no writes happen.
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
pub fn instantiate(deps: DepsMut, _env: Env, info: MessageInfo, msg: InstantiateMsg) -> Result<Response, ContractError> {
    let mut store_ref = StoreRef(deps.storage);
    verified_instantiate(&mut store_ref, &info.sender, msg.total_supply.u128());
    Ok(Response::new().add_attribute("action", "instantiate"))
}

fn map_transfer_error(e: TransferError) -> ContractError {
    match e {
        TransferError::SelfTransfer          => ContractError::SelfTransfer,
        TransferError::Insufficient          => ContractError::Insufficient,
        TransferError::Overflow              => ContractError::Overflow,
        TransferError::InsufficientAllowance => ContractError::InsufficientAllowance,
    }
}

#[entry_point]
pub fn execute(deps: DepsMut, _env: Env, info: MessageInfo, msg: ExecuteMsg) -> Result<Response, ContractError> {
    let mut store_ref = StoreRef(deps.storage);
    match msg {
        ExecuteMsg::Transfer { recipient, amount } => {
            let to = deps.api.addr_validate(&recipient)?;
            verified_transfer(&mut store_ref, &info.sender, &to, amount.u128())
                .map_err(map_transfer_error)?;
            Ok(Response::new()
                .add_attribute("action", "transfer")
                .add_attribute("from", info.sender)
                .add_attribute("to", to)
                .add_attribute("amount", amount.to_string()))
        }
        ExecuteMsg::Approve { spender, amount } => {
            let spender_addr = deps.api.addr_validate(&spender)?;
            verified_approve(&mut store_ref, &info.sender, &spender_addr, amount.u128());
            Ok(Response::new()
                .add_attribute("action", "approve")
                .add_attribute("owner", info.sender)
                .add_attribute("spender", spender_addr)
                .add_attribute("amount", amount.to_string()))
        }
        ExecuteMsg::TransferFrom { owner, recipient, amount } => {
            let owner_addr = deps.api.addr_validate(&owner)?;
            let to         = deps.api.addr_validate(&recipient)?;
            verified_transfer_from(&mut store_ref, &info.sender, &owner_addr, &to, amount.u128())
                .map_err(map_transfer_error)?;
            Ok(Response::new()
                .add_attribute("action", "transfer_from")
                .add_attribute("spender", info.sender)
                .add_attribute("owner", owner_addr)
                .add_attribute("to", to)
                .add_attribute("amount", amount.to_string()))
        }
        ExecuteMsg::Mint { recipient, amount } => {
            // NOTE: a real cw20 would gate this with a Minter-address
            // check. Omitted here to keep the focus on the verified
            // arithmetic + invariant story.
            let to = deps.api.addr_validate(&recipient)?;
            verified_mint(&mut store_ref, &to, amount.u128())
                .map_err(map_transfer_error)?;
            Ok(Response::new()
                .add_attribute("action", "mint")
                .add_attribute("to", to)
                .add_attribute("amount", amount.to_string()))
        }
        ExecuteMsg::Burn { amount } => {
            verified_burn(&mut store_ref, &info.sender, amount.u128())
                .map_err(map_transfer_error)?;
            Ok(Response::new()
                .add_attribute("action", "burn")
                .add_attribute("from", info.sender)
                .add_attribute("amount", amount.to_string()))
        }
        ExecuteMsg::IncreaseAllowance { spender, amount } => {
            let spender_addr = deps.api.addr_validate(&spender)?;
            verified_increase_allowance(&mut store_ref, &info.sender, &spender_addr, amount.u128())
                .map_err(map_transfer_error)?;
            Ok(Response::new()
                .add_attribute("action", "increase_allowance")
                .add_attribute("owner", info.sender)
                .add_attribute("spender", spender_addr)
                .add_attribute("amount", amount.to_string()))
        }
        ExecuteMsg::DecreaseAllowance { spender, amount } => {
            let spender_addr = deps.api.addr_validate(&spender)?;
            verified_decrease_allowance(&mut store_ref, &info.sender, &spender_addr, amount.u128());
            Ok(Response::new()
                .add_attribute("action", "decrease_allowance")
                .add_attribute("owner", info.sender)
                .add_attribute("spender", spender_addr)
                .add_attribute("amount", amount.to_string()))
        }
    }
}

#[entry_point]
pub fn query(deps: Deps, _env: Env, msg: QueryMsg) -> StdResult<Binary> {
    let store_ref = StoreRefRead(deps.storage);
    match msg {
        QueryMsg::BalanceOf { account } => {
            let addr = deps.api.addr_validate(&account)?;
            let b = verified_balance_of(&store_ref, &addr);
            to_json_binary(&Uint128::new(b))
        }
        QueryMsg::TotalSupply {} => to_json_binary(&TOTAL_SUPPLY.load(deps.storage)?),
        QueryMsg::Allowance { owner, spender } => {
            let owner_addr   = deps.api.addr_validate(&owner)?;
            let spender_addr = deps.api.addr_validate(&spender)?;
            let a = verified_allowance(&store_ref, &owner_addr, &spender_addr);
            to_json_binary(&Uint128::new(a))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use cosmwasm_std::testing::{message_info, mock_dependencies, mock_env, MockApi, MockQuerier, MockStorage};
    use cosmwasm_std::{from_json, Addr, OwnedDeps};

    struct Actors { owner: Addr, alice: Addr, bob: Addr }

    fn actors(api: &MockApi) -> Actors {
        Actors {
            owner: api.addr_make("owner"),
            alice: api.addr_make("alice"),
            bob:   api.addr_make("bob"),
        }
    }

    fn setup(supply: u128) -> (OwnedDeps<MockStorage, MockApi, MockQuerier>, Actors) {
        let mut deps = mock_dependencies();
        let a = actors(&deps.api);
        let info = message_info(&a.owner, &[]);
        let msg = InstantiateMsg { total_supply: Uint128::new(supply) };
        instantiate(deps.as_mut(), mock_env(), info, msg).unwrap();
        (deps, a)
    }

    fn balance(deps: Deps, who: &Addr) -> u128 {
        let bin = query(deps, mock_env(), QueryMsg::BalanceOf { account: who.to_string() }).unwrap();
        let amt: Uint128 = from_json(&bin).unwrap();
        amt.u128()
    }

    fn total_supply(deps: Deps) -> u128 {
        let bin = query(deps, mock_env(), QueryMsg::TotalSupply {}).unwrap();
        let amt: Uint128 = from_json(&bin).unwrap();
        amt.u128()
    }

    #[test]
    fn init_supply_credited_to_owner() {
        let (deps, a) = setup(1_000);
        assert_eq!(total_supply(deps.as_ref()), 1_000);
        assert_eq!(balance(deps.as_ref(), &a.owner), 1_000);
    }

    #[test]
    fn balance_of_unknown_is_zero() {
        let (deps, _) = setup(1_000);
        let stranger = deps.api.addr_make("stranger");
        assert_eq!(balance(deps.as_ref(), &stranger), 0);
    }

    #[test]
    fn transfer_happy_path() {
        let (mut deps, a) = setup(1_000);
        let info = message_info(&a.owner, &[]);
        let msg = ExecuteMsg::Transfer { recipient: a.alice.to_string(), amount: Uint128::new(250) };
        execute(deps.as_mut(), mock_env(), info, msg).unwrap();
        assert_eq!(balance(deps.as_ref(), &a.owner), 750);
        assert_eq!(balance(deps.as_ref(), &a.alice), 250);
    }

    #[test]
    fn transfer_insufficient_balance() {
        let (mut deps, a) = setup(100);
        let info = message_info(&a.owner, &[]);
        let msg = ExecuteMsg::Transfer { recipient: a.alice.to_string(), amount: Uint128::new(200) };
        let err = execute(deps.as_mut(), mock_env(), info, msg).unwrap_err();
        assert!(matches!(err, ContractError::Insufficient));
    }

    #[test]
    fn self_transfer_rejected() {
        let (mut deps, a) = setup(1_000);
        let info = message_info(&a.owner, &[]);
        let msg = ExecuteMsg::Transfer { recipient: a.owner.to_string(), amount: Uint128::new(10) };
        let err = execute(deps.as_mut(), mock_env(), info, msg).unwrap_err();
        assert!(matches!(err, ContractError::SelfTransfer));
    }

    #[test]
    fn total_supply_invariant_after_transfer() {
        let (mut deps, a) = setup(1_000);
        let info = message_info(&a.owner, &[]);
        for amt in [100u128, 200, 50] {
            let msg = ExecuteMsg::Transfer { recipient: a.alice.to_string(), amount: Uint128::new(amt) };
            execute(deps.as_mut(), mock_env(), info.clone(), msg).unwrap();
        }
        let sum = balance(deps.as_ref(), &a.owner)
                + balance(deps.as_ref(), &a.alice)
                + balance(deps.as_ref(), &a.bob);
        assert_eq!(sum, total_supply(deps.as_ref()));
    }

    // ---- cw20-style allowance tests ----

    fn allowance(deps: Deps, owner: &Addr, spender: &Addr) -> u128 {
        let bin = query(deps, mock_env(),
            QueryMsg::Allowance { owner: owner.to_string(), spender: spender.to_string() }).unwrap();
        let amt: Uint128 = from_json(&bin).unwrap();
        amt.u128()
    }

    fn approve(deps: &mut OwnedDeps<MockStorage, MockApi, MockQuerier>, owner: &Addr, spender: &Addr, amount: u128) {
        let info = message_info(owner, &[]);
        let msg = ExecuteMsg::Approve { spender: spender.to_string(), amount: Uint128::new(amount) };
        execute(deps.as_mut(), mock_env(), info, msg).unwrap();
    }

    fn transfer_from(deps: &mut OwnedDeps<MockStorage, MockApi, MockQuerier>, spender: &Addr, owner: &Addr, recipient: &Addr, amount: u128) -> Result<(), ContractError> {
        let info = message_info(spender, &[]);
        let msg = ExecuteMsg::TransferFrom {
            owner: owner.to_string(),
            recipient: recipient.to_string(),
            amount: Uint128::new(amount),
        };
        execute(deps.as_mut(), mock_env(), info, msg).map(|_| ())
    }

    #[test]
    fn approve_sets_allowance() {
        let (mut deps, a) = setup(1_000);
        assert_eq!(allowance(deps.as_ref(), &a.owner, &a.alice), 0);
        approve(&mut deps, &a.owner, &a.alice, 250);
        assert_eq!(allowance(deps.as_ref(), &a.owner, &a.alice), 250);
    }

    #[test]
    fn approve_overwrites_previous_allowance() {
        let (mut deps, a) = setup(1_000);
        approve(&mut deps, &a.owner, &a.alice, 250);
        approve(&mut deps, &a.owner, &a.alice, 100);
        assert_eq!(allowance(deps.as_ref(), &a.owner, &a.alice), 100);
    }

    #[test]
    fn transfer_from_happy_path() {
        let (mut deps, a) = setup(1_000);
        approve(&mut deps, &a.owner, &a.alice, 250);
        transfer_from(&mut deps, &a.alice, &a.owner, &a.bob, 200).unwrap();
        assert_eq!(balance(deps.as_ref(), &a.owner), 800);
        assert_eq!(balance(deps.as_ref(), &a.bob), 200);
        // Allowance decreased by exactly amount.
        assert_eq!(allowance(deps.as_ref(), &a.owner, &a.alice), 50);
    }

    #[test]
    fn transfer_from_insufficient_allowance() {
        let (mut deps, a) = setup(1_000);
        approve(&mut deps, &a.owner, &a.alice, 100);
        let err = transfer_from(&mut deps, &a.alice, &a.owner, &a.bob, 200).unwrap_err();
        assert!(matches!(err, ContractError::InsufficientAllowance));
        // Allowance unchanged, balances unchanged.
        assert_eq!(allowance(deps.as_ref(), &a.owner, &a.alice), 100);
        assert_eq!(balance(deps.as_ref(), &a.owner), 1_000);
        assert_eq!(balance(deps.as_ref(), &a.bob), 0);
    }

    #[test]
    fn transfer_from_insufficient_balance_keeps_allowance() {
        let (mut deps, a) = setup(50);
        // Allowance is high but owner only has 50.
        approve(&mut deps, &a.owner, &a.alice, 1_000);
        let err = transfer_from(&mut deps, &a.alice, &a.owner, &a.bob, 200).unwrap_err();
        assert!(matches!(err, ContractError::Insufficient));
        // Allowance untouched on transfer failure.
        assert_eq!(allowance(deps.as_ref(), &a.owner, &a.alice), 1_000);
    }

    #[test]
    fn transfer_from_self_to_self_rejected() {
        let (mut deps, a) = setup(1_000);
        approve(&mut deps, &a.owner, &a.alice, 250);
        let err = transfer_from(&mut deps, &a.alice, &a.owner, &a.owner, 100).unwrap_err();
        assert!(matches!(err, ContractError::SelfTransfer));
    }

    // ---- mint / burn / allowance delta ----

    fn mint(deps: &mut OwnedDeps<MockStorage, MockApi, MockQuerier>, caller: &Addr, recipient: &Addr, amount: u128) -> Result<(), ContractError> {
        let info = message_info(caller, &[]);
        let msg = ExecuteMsg::Mint { recipient: recipient.to_string(), amount: Uint128::new(amount) };
        execute(deps.as_mut(), mock_env(), info, msg).map(|_| ())
    }

    fn burn(deps: &mut OwnedDeps<MockStorage, MockApi, MockQuerier>, caller: &Addr, amount: u128) -> Result<(), ContractError> {
        let info = message_info(caller, &[]);
        let msg = ExecuteMsg::Burn { amount: Uint128::new(amount) };
        execute(deps.as_mut(), mock_env(), info, msg).map(|_| ())
    }

    fn increase_allowance(deps: &mut OwnedDeps<MockStorage, MockApi, MockQuerier>, caller: &Addr, spender: &Addr, amount: u128) -> Result<(), ContractError> {
        let info = message_info(caller, &[]);
        let msg = ExecuteMsg::IncreaseAllowance { spender: spender.to_string(), amount: Uint128::new(amount) };
        execute(deps.as_mut(), mock_env(), info, msg).map(|_| ())
    }

    fn decrease_allowance(deps: &mut OwnedDeps<MockStorage, MockApi, MockQuerier>, caller: &Addr, spender: &Addr, amount: u128) {
        let info = message_info(caller, &[]);
        let msg = ExecuteMsg::DecreaseAllowance { spender: spender.to_string(), amount: Uint128::new(amount) };
        execute(deps.as_mut(), mock_env(), info, msg).unwrap();
    }

    #[test]
    fn mint_increases_supply_and_balance() {
        let (mut deps, a) = setup(1_000);
        mint(&mut deps, &a.owner, &a.alice, 250).unwrap();
        assert_eq!(total_supply(deps.as_ref()), 1_250);
        assert_eq!(balance(deps.as_ref(), &a.alice), 250);
        assert_eq!(balance(deps.as_ref(), &a.owner), 1_000); // unchanged
    }

    #[test]
    fn burn_decreases_supply_and_balance() {
        let (mut deps, a) = setup(1_000);
        burn(&mut deps, &a.owner, 250).unwrap();
        assert_eq!(total_supply(deps.as_ref()), 750);
        assert_eq!(balance(deps.as_ref(), &a.owner), 750);
    }

    #[test]
    fn burn_insufficient_balance() {
        let (mut deps, a) = setup(100);
        let err = burn(&mut deps, &a.owner, 200).unwrap_err();
        assert!(matches!(err, ContractError::Insufficient));
        assert_eq!(total_supply(deps.as_ref()), 100); // unchanged
        assert_eq!(balance(deps.as_ref(), &a.owner), 100);
    }

    #[test]
    fn mint_burn_round_trip_preserves_supply() {
        let (mut deps, a) = setup(1_000);
        mint(&mut deps, &a.owner, &a.alice, 250).unwrap();
        burn(&mut deps, &a.alice, 250).unwrap();
        assert_eq!(total_supply(deps.as_ref()), 1_000);
        assert_eq!(balance(deps.as_ref(), &a.alice), 0);
    }

    #[test]
    fn increase_allowance_adds_to_current() {
        let (mut deps, a) = setup(1_000);
        approve(&mut deps, &a.owner, &a.alice, 100);
        increase_allowance(&mut deps, &a.owner, &a.alice, 50).unwrap();
        assert_eq!(allowance(deps.as_ref(), &a.owner, &a.alice), 150);
    }

    #[test]
    fn decrease_allowance_subtracts_saturating_at_zero() {
        let (mut deps, a) = setup(1_000);
        approve(&mut deps, &a.owner, &a.alice, 100);
        decrease_allowance(&mut deps, &a.owner, &a.alice, 30);
        assert_eq!(allowance(deps.as_ref(), &a.owner, &a.alice), 70);
        // Saturating: decrease past zero clamps.
        decrease_allowance(&mut deps, &a.owner, &a.alice, 999);
        assert_eq!(allowance(deps.as_ref(), &a.owner, &a.alice), 0);
    }

    #[test]
    fn conservation_after_mixed_ops() {
        // The invariant sum(balances) == total_supply should hold across
        // any sequence of valid operations, including mint and burn.
        let (mut deps, a) = setup(1_000);
        mint(&mut deps, &a.owner, &a.alice, 500).unwrap();         // supply: 1500
        transfer_from_via_approval(&mut deps, &a);                 // alice approves bob
        burn(&mut deps, &a.alice, 100).unwrap();                   // supply: 1400
        increase_allowance(&mut deps, &a.alice, &a.bob, 50).unwrap();

        let sum = balance(deps.as_ref(), &a.owner)
                + balance(deps.as_ref(), &a.alice)
                + balance(deps.as_ref(), &a.bob);
        assert_eq!(sum, total_supply(deps.as_ref()));
    }

    fn transfer_from_via_approval(deps: &mut OwnedDeps<MockStorage, MockApi, MockQuerier>, a: &Actors) {
        approve(deps, &a.alice, &a.bob, 100);
        transfer_from(deps, &a.bob, &a.alice, &a.owner, 50).unwrap();
    }
}
