// Verified kernels that the CosmWasm entry points forward to.
//
// Same pattern as `verified_state.rs` in the linera_alternate fungible
// example: the SDK-decorated `instantiate` / `execute` / `query` glue
// is a thin forwarder; all of the substantive logic — caller checks,
// arithmetic, allowance handling, mint/burn authorisation — lives here
// with `ensures` clauses that pin the effect on the ghost `*_view`
// projections from `cw_axioms.rs`.

use cosmwasm_std::{Addr, Storage};

pub use verus_fungible_core::TransferError;

use crate::cw_axioms::{
    ax_allowances_load, ax_allowances_save, ax_balances_load, ax_balances_save,
    ax_minter_load, ax_minter_save, ax_supply_load, ax_supply_save,
};

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
