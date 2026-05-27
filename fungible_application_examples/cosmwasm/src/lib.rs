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
    ax_minter_load, ax_minter_save,
};

// -- Verified transfer helper ------------------------------------------
//
// Single function that captures every substantive step of the contract's
// `Transfer` execute branch: caller/recipient comparison, balance reads,
// arithmetic via the verified `core::transfer_balances`, balance writes.
// The `ensures` clause pins down the storage effect on the abstract
// `balances_view` of `Storage`, using the axioms in `cw_axioms.rs`.

// TransferError, balance_at, transfer_balances_map, nat_balances, and the
// state-refinement lemmas (lemma_balance_map_{transfer,mint,burn}_matches_state)
// all live in `verus_fungible_core` and are re-used here unchanged.
pub use verus_fungible_core::TransferError;

vstd::prelude::verus! {
    #[cfg(verus_only)]
    use vstd::prelude::*;
    #[cfg(verus_only)]
    use vstd::map::Map as SpecMap;
    #[cfg(verus_only)]
    use crate::cw_axioms::{balances_view, supply_view, allowances_view, minter_view};
    #[cfg(verus_only)]
    use verus_fungible_core::{
        balance_at, transfer_balances_map, nat_balances,
        lemma_balance_map_transfer_matches_state,
        lemma_balance_map_mint_matches_state,
        lemma_balance_map_burn_matches_state,
    };

    /// Verified transfer step: ensures the storage update matches
    /// `transfer_balances_map` on success, leaves storage untouched on
    /// error. `supply_view` and `allowances_view` are preserved either
    /// way (transfers only touch balances).
    ///
    /// On success, when both `sender` and `receiver` are present in the
    /// pre-state, the storage update also matches `core::state_after_transfer`'s
    /// balance field (via `lemma_verified_transfer_matches_state`), so
    /// callers can chain to the core conservation theorem.
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
                    && allowances_view(final(storage)) == allowances_view(old(storage))
                    // State-level connection (conditional on lemma's preconditions).
                    && (balances_view(old(storage)).dom().contains(*sender)
                        && balances_view(old(storage)).dom().contains(*receiver)
                        && balances_view(old(storage))[*receiver] as int + amount as int <= u128::MAX as int
                        ==>
                        nat_balances(balances_view(final(storage)))
                            == crate::core::state_after_transfer(
                                crate::core::State {
                                    total_supply: 0nat,
                                    balances:     nat_balances(balances_view(old(storage))),
                                },
                                *sender, *receiver, amount as nat,
                            ).balances),
                Err(_) => true,
            },
    {
        if *sender == *receiver {
            return Err(TransferError::SelfTransfer);
        }
        let from = ax_balances_load(storage, sender);
        let to   = ax_balances_load(storage, receiver);
        proof {
            assert(from == balance_at(balances_view(old(storage)), *sender));
            assert(to   == balance_at(balances_view(old(storage)), *receiver));
        }
        match crate::core::transfer_balances(from, to, amount) {
            Ok((from_next, to_next)) => {
                ax_balances_save(storage, sender, from_next);
                proof {
                    assert(balance_at(balances_view(storage), *receiver) == to);
                }
                ax_balances_save(storage, receiver, to_next);
                proof {
                    // Invoke the refinement lemma when its preconditions hold,
                    // so the state-level ensures is satisfied.
                    let pre = balances_view(old(storage));
                    if pre.dom().contains(*sender)
                       && pre.dom().contains(*receiver)
                       && pre[*receiver] as int + amount as int <= u128::MAX as int
                    {
                        lemma_balance_map_transfer_matches_state(pre, *sender, *receiver, amount);
                    }
                }
                Ok(())
            }
            Err(_msg) => {
                if from < amount { Err(TransferError::Insufficient) }
                else             { Err(TransferError::Overflow) }
            }
        }
    }

    /// Verified instantiate step: sets `TOTAL_SUPPLY`, credits the owner
    /// with the full supply, and records `minter` as the authorized
    /// minter. The `ensures` pins down the resulting storage delta.
    pub fn verified_instantiate<S: Storage>(
        storage:      &mut S,
        owner:        &Addr,
        minter:       &Addr,
        total_supply: u128,
    )
        ensures
            supply_view(final(storage)) == total_supply,
            balances_view(final(storage))
                == balances_view(old(storage)).insert(*owner, total_supply),
            minter_view(final(storage)) == Some(*minter),
    {
        ax_supply_save(storage, total_supply);
        ax_balances_save(storage, owner, total_supply);
        ax_minter_save(storage, minter);
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

    // -- Mint & burn ----------------------------------------------------

    /// Verified `mint`: credits `amount` to `to` and increases
    /// `total_supply`. Authorization: the caller must match the stored
    /// minter (set at `verified_instantiate` time). On `Ok`, the storage
    /// update matches `core::state_after_mint`; on `Err`, storage is
    /// untouched.
    pub fn verified_mint<S: Storage>(
        storage: &mut S,
        caller:  &Addr,
        to:      &Addr,
        amount:  u128,
    ) -> (r: Result<(), TransferError>)
        ensures
            match r {
                Ok(()) =>
                    minter_view(old(storage)) == Some(*caller)
                    && supply_view(final(storage))
                        == (supply_view(old(storage)) + amount) as u128
                    && balances_view(final(storage))
                        == balances_view(old(storage)).insert(
                            *to,
                            (balance_at(balances_view(old(storage)), *to) + amount) as u128,
                        )
                    && allowances_view(final(storage)) == allowances_view(old(storage))
                    && minter_view(final(storage)) == minter_view(old(storage))
                    // State-level connection (conditional).
                    && (balances_view(old(storage)).dom().contains(*to)
                        && balances_view(old(storage))[*to] as int + amount as int <= u128::MAX as int
                        ==>
                        nat_balances(balances_view(final(storage)))
                            == crate::core::state_after_mint(
                                crate::core::State {
                                    total_supply: supply_view(old(storage)) as nat,
                                    balances:     nat_balances(balances_view(old(storage))),
                                },
                                *to, amount as nat,
                            ).balances),
                Err(_) => true,
            },
    {
        // Authorization: caller must be the registered minter.
        match ax_minter_load(storage) {
            Some(m) if m == *caller => {}
            _ => return Err(TransferError::Unauthorized),
        }
        let supply = ax_supply_load(storage);
        let bal    = ax_balances_load(storage, to);
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
        proof {
            let pre = balances_view(old(storage));
            let pre_supply = supply_view(old(storage));
            if pre.dom().contains(*to) && pre[*to] as int + amount as int <= u128::MAX as int {
                lemma_balance_map_mint_matches_state(pre, pre_supply, *to, amount);
            }
        }
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
                    && allowances_view(final(storage)) == allowances_view(old(storage))
                    && minter_view(final(storage)) == minter_view(old(storage))
                    // State-level connection (conditional).
                    && (balances_view(old(storage)).dom().contains(*from)
                        && balances_view(old(storage))[*from] >= amount
                        && supply_view(old(storage)) >= amount
                        ==>
                        nat_balances(balances_view(final(storage)))
                            == crate::core::state_after_burn(
                                crate::core::State {
                                    total_supply: supply_view(old(storage)) as nat,
                                    balances:     nat_balances(balances_view(old(storage))),
                                },
                                *from, amount as nat,
                            ).balances),
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
        proof {
            let pre = balances_view(old(storage));
            let pre_supply = supply_view(old(storage));
            if pre.dom().contains(*from) && pre[*from] >= amount && pre_supply >= amount {
                lemma_balance_map_burn_matches_state(pre, pre_supply, *from, amount);
            }
        }
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

    /// Verified `update_minter`: change the registered minter. The caller
    /// must be the current minter. On `Ok`, only `minter_view` changes.
    pub fn verified_update_minter<S: Storage>(
        storage:    &mut S,
        caller:     &Addr,
        new_minter: &Addr,
    ) -> (r: Result<(), TransferError>)
        ensures
            match r {
                Ok(()) =>
                    minter_view(old(storage)) == Some(*caller)
                    && minter_view(final(storage))     == Some(*new_minter)
                    && balances_view(final(storage))   == balances_view(old(storage))
                    && supply_view(final(storage))     == supply_view(old(storage))
                    && allowances_view(final(storage)) == allowances_view(old(storage)),
                Err(_) => true,
            },
    {
        match ax_minter_load(storage) {
            Some(m) if m == *caller => {}
            _ => return Err(TransferError::Unauthorized),
        }
        ax_minter_save(storage, new_minter);
        Ok(())
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
    /// Optional minter address. If absent, defaults to the instantiator,
    /// matching cw20's convention.
    pub minter: Option<String>,
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
    UpdateMinter      { new_minter: String },
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
    #[error("unauthorized")]              Unauthorized,
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
    // Default minter = instantiator (matches cw20 convention).
    let minter = match msg.minter {
        Some(s) => deps.api.addr_validate(&s)?,
        None    => info.sender.clone(),
    };
    let mut store_ref = StoreRef(deps.storage);
    verified_instantiate(&mut store_ref, &info.sender, &minter, msg.total_supply.u128());
    Ok(Response::new()
        .add_attribute("action", "instantiate")
        .add_attribute("minter", minter))
}

fn map_transfer_error(e: TransferError) -> ContractError {
    match e {
        TransferError::SelfTransfer          => ContractError::SelfTransfer,
        TransferError::Insufficient          => ContractError::Insufficient,
        TransferError::Overflow              => ContractError::Overflow,
        TransferError::InsufficientAllowance => ContractError::InsufficientAllowance,
        TransferError::InsufficientSupply    => ContractError::Insufficient,
        TransferError::Unauthorized          => ContractError::Unauthorized,
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
            let to = deps.api.addr_validate(&recipient)?;
            verified_mint(&mut store_ref, &info.sender, &to, amount.u128())
                .map_err(map_transfer_error)?;
            Ok(Response::new()
                .add_attribute("action", "mint")
                .add_attribute("by", info.sender)
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
        ExecuteMsg::UpdateMinter { new_minter } => {
            let new_minter_addr = deps.api.addr_validate(&new_minter)?;
            verified_update_minter(&mut store_ref, &info.sender, &new_minter_addr)
                .map_err(map_transfer_error)?;
            Ok(Response::new()
                .add_attribute("action", "update_minter")
                .add_attribute("by", info.sender)
                .add_attribute("new_minter", new_minter_addr))
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
        let msg = InstantiateMsg { total_supply: Uint128::new(supply), minter: None };
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

    // ---- minter authorization ----

    #[test]
    fn mint_by_non_minter_unauthorized() {
        // Default minter is the instantiator (owner). alice tries to mint.
        let (mut deps, a) = setup(1_000);
        let err = mint(&mut deps, &a.alice, &a.bob, 100).unwrap_err();
        assert!(matches!(err, ContractError::Unauthorized));
        // State unchanged.
        assert_eq!(total_supply(deps.as_ref()), 1_000);
        assert_eq!(balance(deps.as_ref(), &a.bob), 0);
    }

    #[test]
    fn mint_by_minter_works() {
        let (mut deps, a) = setup(1_000);
        // Owner is the default minter.
        mint(&mut deps, &a.owner, &a.bob, 250).unwrap();
        assert_eq!(total_supply(deps.as_ref()), 1_250);
        assert_eq!(balance(deps.as_ref(), &a.bob), 250);
    }

    fn update_minter(deps: &mut OwnedDeps<MockStorage, MockApi, MockQuerier>, caller: &Addr, new_minter: &Addr) -> Result<(), ContractError> {
        let info = message_info(caller, &[]);
        let msg = ExecuteMsg::UpdateMinter { new_minter: new_minter.to_string() };
        execute(deps.as_mut(), mock_env(), info, msg).map(|_| ())
    }

    #[test]
    fn update_minter_by_current_minter() {
        let (mut deps, a) = setup(1_000);
        // Owner is default minter. Transfer to alice.
        update_minter(&mut deps, &a.owner, &a.alice).unwrap();
        // Owner can no longer mint; alice can.
        assert!(matches!(mint(&mut deps, &a.owner, &a.bob, 50).unwrap_err(), ContractError::Unauthorized));
        mint(&mut deps, &a.alice, &a.bob, 50).unwrap();
        assert_eq!(balance(deps.as_ref(), &a.bob), 50);
    }

    #[test]
    fn update_minter_by_non_minter_rejected() {
        let (mut deps, a) = setup(1_000);
        let err = update_minter(&mut deps, &a.alice, &a.bob).unwrap_err();
        assert!(matches!(err, ContractError::Unauthorized));
    }

    #[test]
    fn explicit_minter_in_instantiate() {
        // Set alice as the minter instead of the instantiator (owner).
        let mut deps = mock_dependencies();
        let a = actors(&deps.api);
        let info = message_info(&a.owner, &[]);
        let msg = InstantiateMsg {
            total_supply: Uint128::new(1_000),
            minter: Some(a.alice.to_string()),
        };
        instantiate(deps.as_mut(), mock_env(), info, msg).unwrap();
        // Owner can't mint now.
        let err = mint(&mut deps, &a.owner, &a.bob, 100).unwrap_err();
        assert!(matches!(err, ContractError::Unauthorized));
        // Alice can.
        mint(&mut deps, &a.alice, &a.bob, 100).unwrap();
        assert_eq!(balance(deps.as_ref(), &a.bob), 100);
    }
}
