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
    pub balances: BTreeMap<Principal, u128>,
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
}

#[init]
fn init(owner: Principal, total_supply: u128) {
    STATE.with(|s| {
        let mut state = s.borrow_mut();
        state.total_supply = total_supply;
        state.balances.insert(owner, total_supply);
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

#[update]
fn transfer(to: Principal, amount: u128) -> Result<(), String> {
    STATE.with(|s| {
        let mut state = s.borrow_mut();
        match verified_transfer(&mut state.balances, to, amount) {
            Ok(())                                 => Ok(()),
            Err(TransferError::SelfTransfer)       => Err("self-transfer".into()),
            Err(TransferError::Insufficient)       => Err("insufficient balance".into()),
            Err(TransferError::Overflow)           => Err("balance overflow".into()),
        }
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
