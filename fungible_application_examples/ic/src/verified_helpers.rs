// Verified kernels that the IC entry points (`#[update]` / `#[query]`)
// forward to.
//
// Same pattern as `verified_state.rs` in the linera_alternate fungible
// example: the SDK-decorated entry points are thin forwarders; the
// substantive logic — caller checks via `the_caller()`, arithmetic,
// allowance handling, mint/burn authorisation — lives here with
// `ensures` clauses on the abstract `@`-projected view of each
// BTreeMap.
//
// The BTreeMap point-op wrappers (`read_balance`, `save_balance`,
// `read_allowance`, `save_allowance`) also live here because they're
// part of the verified helpers' trust surface and consumed only by
// these helpers.

use candid::Principal;
use std::collections::BTreeMap;

use crate::ic_axioms::caller;
pub use verus_fungible_core::TransferError;

vstd::prelude::verus! {
    #[cfg(verus_only)]
    use vstd::prelude::*;
    #[cfg(verus_only)]
    use vstd::map::Map as SpecMap;
    #[cfg(verus_only)]
    use crate::ic_axioms::the_caller;
    #[cfg(verus_only)]
    use verus_fungible_core::{balance_at, transfer_balances_map};

    // -- BTreeMap point-op wrappers ------------------------------------
    //
    // vstd has assume_specifications for `BTreeMap::{get, insert, ...}`
    // but they use Borrow<Q>-based predicates that complicate Verus's
    // reasoning for our use case. These thin wrappers expose the same
    // operations with the simpler `m@.dom().contains(k)` / `m@[k]` shape
    // we use everywhere else in the project. Trusted (external_body) —
    // each wrapper is a one-line delegation to BTreeMap.
    #[verifier::external_body]
    pub fn read_balance(m: &BTreeMap<Principal, u128>, k: &Principal) -> (r: u128)
        ensures r == balance_at(m@, *k),
    {
        m.get(k).copied().unwrap_or(0)
    }

    #[verifier::external_body]
    pub fn save_balance(m: &mut BTreeMap<Principal, u128>, k: Principal, v: u128)
        ensures final(m)@ == old(m)@.insert(k, v),
    {
        m.insert(k, v);
    }

    /// Allowance at (owner, spender) — default 0 if absent.
    pub open spec fn allowance_at(
        m: SpecMap<(Principal, Principal), u128>,
        owner: Principal,
        spender: Principal,
    ) -> u128 {
        if m.dom().contains((owner, spender)) { m[(owner, spender)] } else { 0u128 }
    }

    #[verifier::external_body]
    pub fn read_allowance(m: &BTreeMap<(Principal, Principal), u128>, owner: &Principal, spender: &Principal) -> (r: u128)
        ensures r == allowance_at(m@, *owner, *spender),
    {
        m.get(&(*owner, *spender)).copied().unwrap_or(0)
    }

    #[verifier::external_body]
    pub fn save_allowance(m: &mut BTreeMap<(Principal, Principal), u128>, owner: Principal, spender: Principal, v: u128)
        ensures final(m)@ == old(m)@.insert((owner, spender), v),
    {
        m.insert((owner, spender), v);
    }

    /// Verified transfer step: reads the caller via the axiomatized
    /// `caller()`, rejects self-transfer, then mutates the balances map.
    /// `ensures` describes the resulting state on the abstract view.
    pub fn verified_transfer(
        balances: &mut BTreeMap<Principal, u128>,
        receiver: Principal,
        amount:   u128,
    ) -> (r: Result<(), TransferError>)
        ensures
            match r {
                Ok(()) =>
                    the_caller() != receiver
                    && final(balances)@
                        == transfer_balances_map(old(balances)@, the_caller(), receiver, amount),
                Err(_) => true,
            },
    {
        let sender = caller();
        if sender == receiver {
            return Err(TransferError::SelfTransfer);
        }
        let from = read_balance(balances, &sender);
        let to   = read_balance(balances, &receiver);
        match crate::core::transfer_balances(from, to, amount) {
            Ok((from_next, to_next)) => {
                save_balance(balances, sender, from_next);
                proof {
                    assert(balance_at(balances@, receiver) == to);
                }
                save_balance(balances, receiver, to_next);
                Ok(())
            }
            Err(_msg) => {
                if from < amount { Err(TransferError::Insufficient) }
                else             { Err(TransferError::Overflow) }
            }
        }
    }

    // -- Approve / TransferFrom ----------------------------------------

    /// Set the (caller, spender) allowance to exactly `amount`.
    pub fn verified_approve(
        allowances: &mut BTreeMap<(Principal, Principal), u128>,
        spender:    Principal,
        amount:     u128,
    )
        ensures
            final(allowances)@
                == old(allowances)@.insert((the_caller(), spender), amount),
    {
        let owner = caller();
        save_allowance(allowances, owner, spender, amount);
    }

    /// Move `amount` from `owner` to `recipient` using the caller's
    /// allowance. On `Ok`: balances updated, allowance decremented. On
    /// `Err`: state unchanged.
    pub fn verified_transfer_from(
        balances:   &mut BTreeMap<Principal, u128>,
        allowances: &mut BTreeMap<(Principal, Principal), u128>,
        owner:      Principal,
        recipient:  Principal,
        amount:     u128,
    ) -> (r: Result<(), TransferError>)
        ensures
            match r {
                Ok(()) =>
                    owner != recipient
                    && final(balances)@
                        == transfer_balances_map(old(balances)@, owner, recipient, amount)
                    && final(allowances)@
                        == old(allowances)@.insert(
                            (owner, the_caller()),
                            (allowance_at(old(allowances)@, owner, the_caller()) - amount) as u128,
                        ),
                Err(_) => true,
            },
    {
        let spender = caller();
        if owner == recipient {
            return Err(TransferError::SelfTransfer);
        }
        let current_allowance = read_allowance(allowances, &owner, &spender);
        if current_allowance < amount {
            return Err(TransferError::InsufficientAllowance);
        }
        let from = read_balance(balances, &owner);
        let to   = read_balance(balances, &recipient);
        match crate::core::transfer_balances(from, to, amount) {
            Ok((from_next, to_next)) => {
                save_balance(balances, owner, from_next);
                proof {
                    assert(balance_at(balances@, recipient) == to);
                }
                save_balance(balances, recipient, to_next);
                save_allowance(allowances, owner, spender, current_allowance - amount);
                Ok(())
            }
            Err(_msg) => {
                if from < amount { Err(TransferError::Insufficient) }
                else             { Err(TransferError::Overflow) }
            }
        }
    }

    // -- Mint / Burn ---------------------------------------------------

    /// Mint `amount` to `to`. Caller must be the registered minter.
    pub fn verified_mint(
        balances:     &mut BTreeMap<Principal, u128>,
        total_supply: &mut u128,
        minter:       &Option<Principal>,
        to:           Principal,
        amount:       u128,
    ) -> (r: Result<(), TransferError>)
        ensures
            match r {
                Ok(()) =>
                    *minter == Some(the_caller())
                    && *final(total_supply) == (*old(total_supply) + amount) as u128
                    && final(balances)@
                        == old(balances)@.insert(
                            to,
                            (balance_at(old(balances)@, to) + amount) as u128,
                        ),
                Err(_) => true,
            },
    {
        let c = caller();
        // Authorization: caller must be the registered minter.
        let is_minter = match minter {
            Some(m) => *m == c,
            None    => false,
        };
        if !is_minter {
            return Err(TransferError::Unauthorized);
        }
        let new_supply = match total_supply.checked_add(amount) {
            Some(v) => v,
            None    => return Err(TransferError::Overflow),
        };
        let bal = read_balance(balances, &to);
        let new_bal = match bal.checked_add(amount) {
            Some(v) => v,
            None    => return Err(TransferError::Overflow),
        };
        *total_supply = new_supply;
        save_balance(balances, to, new_bal);
        Ok(())
    }

    /// Burn `amount` from the caller's balance.
    pub fn verified_burn(
        balances:     &mut BTreeMap<Principal, u128>,
        total_supply: &mut u128,
        amount:       u128,
    ) -> (r: Result<(), TransferError>)
        ensures
            match r {
                Ok(()) =>
                    *final(total_supply) == (*old(total_supply) - amount) as u128
                    && final(balances)@
                        == old(balances)@.insert(
                            the_caller(),
                            (balance_at(old(balances)@, the_caller()) - amount) as u128,
                        ),
                Err(_) => true,
            },
    {
        let from = caller();
        let bal = read_balance(balances, &from);
        let new_bal = match bal.checked_sub(amount) {
            Some(v) => v,
            None    => return Err(TransferError::Insufficient),
        };
        let new_supply = match total_supply.checked_sub(amount) {
            Some(v) => v,
            None    => return Err(TransferError::Insufficient),
        };
        *total_supply = new_supply;
        save_balance(balances, from, new_bal);
        Ok(())
    }

    // -- Allowance delta -----------------------------------------------

    pub fn verified_increase_allowance(
        allowances: &mut BTreeMap<(Principal, Principal), u128>,
        spender:    Principal,
        amount:     u128,
    ) -> (r: Result<(), TransferError>)
        ensures
            match r {
                Ok(()) =>
                    final(allowances)@
                        == old(allowances)@.insert(
                            (the_caller(), spender),
                            (allowance_at(old(allowances)@, the_caller(), spender) + amount) as u128,
                        ),
                Err(_) => true,
            },
    {
        let owner = caller();
        let current = read_allowance(allowances, &owner, &spender);
        match current.checked_add(amount) {
            Some(new) => {
                save_allowance(allowances, owner, spender, new);
                Ok(())
            }
            None => Err(TransferError::Overflow),
        }
    }

    pub fn verified_decrease_allowance(
        allowances: &mut BTreeMap<(Principal, Principal), u128>,
        spender:    Principal,
        amount:     u128,
    )
        ensures
            final(allowances)@
                == old(allowances)@.insert(
                    (the_caller(), spender),
                    if allowance_at(old(allowances)@, the_caller(), spender) >= amount {
                        (allowance_at(old(allowances)@, the_caller(), spender) - amount) as u128
                    } else {
                        0u128
                    },
                ),
    {
        let owner = caller();
        let current = read_allowance(allowances, &owner, &spender);
        let new = if current >= amount { current - amount } else { 0u128 };
        save_allowance(allowances, owner, spender, new);
    }

    // -- Update minter --------------------------------------------------

    pub fn verified_update_minter(
        minter:     &mut Option<Principal>,
        new_minter: Principal,
    ) -> (r: Result<(), TransferError>)
        ensures
            match r {
                Ok(()) =>
                    *old(minter) == Some(the_caller())
                    && *final(minter) == Some(new_minter),
                Err(_) => true,
            },
    {
        let c = caller();
        let is_minter = match minter {
            Some(m) => *m == c,
            None    => false,
        };
        if !is_minter {
            return Err(TransferError::Unauthorized);
        }
        *minter = Some(new_minter);
        Ok(())
    }
}
