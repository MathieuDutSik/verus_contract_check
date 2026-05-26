// IC fungible-token contract with Verus-verified core arithmetic and
// storage refinement.
//
// Layout:
//   - `pub mod core;`        — chain-agnostic State<A> + conservation
//                              lemmas (identical to the NEAR/CosmWasm
//                              core).
//   - `pub mod ic_axioms;`   — IC-specific axioms: Principal external
//                              type, `caller()`/`trap()` wrappers tying
//                              into the ghost `the_caller()`.
//   - this file              — the actual contract: `State` struct,
//                              verified helpers, #[init]/#[update]/#[query]
//                              entry points.
//
// Build modes:
//   cargo build              — wasm canister artifact.
//   cargo test               — runs the 6 logic tests.
//   cargo verus verify --target wasm32-unknown-unknown
//                            — verifies the core arithmetic, conservation
//                              lemmas, and the verified runtime helpers.

pub mod core;
pub mod ic_axioms;

use candid::{CandidType, Principal};
use ic_cdk_macros::{init, query, update};
use serde::Deserialize;
use std::cell::RefCell;
use std::collections::BTreeMap;

use crate::ic_axioms::caller;

#[derive(Default, CandidType, Deserialize)]
pub struct State {
    pub total_supply: u128,
    pub balances:     BTreeMap<Principal, u128>,
    pub allowances:   BTreeMap<(Principal, Principal), u128>,
    pub minter:       Option<Principal>,
}

thread_local! { static STATE: RefCell<State> = RefCell::new(State::default()); }

// Verified helpers — all the substantive logic lives here, proven against
// vstd's BTreeMap axioms.
vstd::prelude::verus! {
    #[cfg(verus_only)]
    use vstd::prelude::*;
    #[cfg(verus_only)]
    use vstd::map::Map as SpecMap;
    #[cfg(verus_only)]
    use crate::ic_axioms::the_caller;

    /// Failure modes of the verified helpers.
    #[derive(PartialEq, Eq)]
    pub enum TransferError {
        SelfTransfer,
        Insufficient,
        Overflow,
        InsufficientAllowance,
        Unauthorized,
    }

    /// Balance of `k` in the abstract map, with absent entries treated as 0.
    pub open spec fn balance_at(m: SpecMap<Principal, u128>, k: Principal) -> u128 {
        if m.dom().contains(k) { m[k] } else { 0u128 }
    }

    /// The map after a transfer's balance update.
    pub open spec fn transfer_balances_map(
        m: SpecMap<Principal, u128>,
        sender: Principal,
        receiver: Principal,
        amount: u128,
    ) -> SpecMap<Principal, u128> {
        m.insert(sender,   (balance_at(m, sender) - amount) as u128)
         .insert(receiver, (balance_at(m, receiver) + amount) as u128)
    }

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

fn err_to_string(e: TransferError) -> String {
    match e {
        TransferError::SelfTransfer          => "self-transfer".into(),
        TransferError::Insufficient          => "insufficient balance".into(),
        TransferError::Overflow              => "balance overflow".into(),
        TransferError::InsufficientAllowance => "insufficient allowance".into(),
        TransferError::Unauthorized          => "unauthorized".into(),
    }
}

#[init]
fn init(owner: Principal, total_supply: u128, minter: Option<Principal>) {
    STATE.with(|s| {
        let mut state = s.borrow_mut();
        state.total_supply = total_supply;
        state.balances.insert(owner, total_supply);
        state.minter = Some(minter.unwrap_or(owner));
    });
}

#[query]
fn balance_of(account: Principal) -> u128 {
    STATE.with(|s| s.borrow().balances.get(&account).copied().unwrap_or(0))
}

#[query]
fn total_supply() -> u128 {
    STATE.with(|s| s.borrow().total_supply)
}

#[query]
fn allowance(owner: Principal, spender: Principal) -> u128 {
    STATE.with(|s| s.borrow().allowances.get(&(owner, spender)).copied().unwrap_or(0))
}

#[query]
fn minter() -> Option<Principal> {
    STATE.with(|s| s.borrow().minter)
}

#[update]
fn transfer(to: Principal, amount: u128) -> Result<(), String> {
    STATE.with(|s| {
        let mut state = s.borrow_mut();
        verified_transfer(&mut state.balances, to, amount).map_err(err_to_string)
    })
}

#[update]
fn approve(spender: Principal, amount: u128) {
    STATE.with(|s| {
        let mut state = s.borrow_mut();
        verified_approve(&mut state.allowances, spender, amount);
    });
}

#[update]
fn transfer_from(owner: Principal, recipient: Principal, amount: u128) -> Result<(), String> {
    STATE.with(|s| {
        let mut state = s.borrow_mut();
        let State { balances, allowances, .. } = &mut *state;
        verified_transfer_from(balances, allowances, owner, recipient, amount).map_err(err_to_string)
    })
}

#[update]
fn mint(to: Principal, amount: u128) -> Result<(), String> {
    STATE.with(|s| {
        let mut state = s.borrow_mut();
        let State { balances, total_supply, minter, .. } = &mut *state;
        verified_mint(balances, total_supply, minter, to, amount).map_err(err_to_string)
    })
}

#[update]
fn burn(amount: u128) -> Result<(), String> {
    STATE.with(|s| {
        let mut state = s.borrow_mut();
        let State { balances, total_supply, .. } = &mut *state;
        verified_burn(balances, total_supply, amount).map_err(err_to_string)
    })
}

#[update]
fn increase_allowance(spender: Principal, amount: u128) -> Result<(), String> {
    STATE.with(|s| {
        let mut state = s.borrow_mut();
        verified_increase_allowance(&mut state.allowances, spender, amount).map_err(err_to_string)
    })
}

#[update]
fn decrease_allowance(spender: Principal, amount: u128) {
    STATE.with(|s| {
        let mut state = s.borrow_mut();
        verified_decrease_allowance(&mut state.allowances, spender, amount);
    });
}

#[update]
fn update_minter(new_minter: Principal) -> Result<(), String> {
    STATE.with(|s| {
        let mut state = s.borrow_mut();
        verified_update_minter(&mut state.minter, new_minter).map_err(err_to_string)
    })
}

ic_cdk::export_candid!();

#[cfg(test)]
mod tests {
    use super::*;

    fn p(b: u8) -> Principal { Principal::from_slice(&[b; 29]) }

    fn fresh_balances() -> BTreeMap<Principal, u128> {
        let mut b = BTreeMap::new();
        b.insert(p(1), 1_000);
        b
    }

    #[test]
    fn balance_of_unknown_is_zero() {
        let b = fresh_balances();
        assert_eq!(b.get(&p(42)).copied().unwrap_or(0), 0);
    }

    #[test]
    fn transfer_happy_path_via_state() {
        // We can't call `verified_transfer` directly from tests because
        // it uses the IC env's `caller()`. Test the underlying logic on
        // the balances map.
        let mut b = fresh_balances();
        let owner = p(1);
        let alice = p(2);
        let from = *b.get(&owner).unwrap();
        let to   = b.get(&alice).copied().unwrap_or(0);
        let (from_next, to_next) = core::transfer_balances(from, to, 250).unwrap();
        b.insert(owner, from_next);
        b.insert(alice, to_next);
        assert_eq!(b.get(&owner).copied().unwrap_or(0), 750);
        assert_eq!(b.get(&alice).copied().unwrap_or(0), 250);
    }

    #[test]
    fn transfer_insufficient_balance() {
        assert!(core::transfer_balances(100, 0, 200).is_err());
    }

    #[test]
    fn total_supply_invariant_after_transfers() {
        let mut b = fresh_balances();
        let owner = p(1);
        let alice = p(2);
        let bob   = p(3);
        for amt in [100u128, 200, 50] {
            let from = *b.get(&owner).unwrap_or(&0);
            let to   = b.get(&alice).copied().unwrap_or(0);
            let (fn_, tn) = core::transfer_balances(from, to, amt).unwrap();
            b.insert(owner, fn_);
            b.insert(alice, tn);
        }
        let sum = b.get(&owner).copied().unwrap_or(0)
                + b.get(&alice).copied().unwrap_or(0)
                + b.get(&bob).copied().unwrap_or(0);
        assert_eq!(sum, 1_000);
    }
}
