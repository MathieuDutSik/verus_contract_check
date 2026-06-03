// IC fungible-token contract with Verus-verified core arithmetic and
// storage refinement.
//
// Layout (mirrors `linera_alternate` fungible):
//   - `pub mod core;`              — chain-agnostic verified core.
//   - `pub mod ic_axioms;`         — Principal external type spec +
//                                    `caller()` / `trap()` wrappers
//                                    + `the_caller()` ghost.
//   - `pub mod verified_helpers;`  — all `verified_*` functions and
//                                    the BTreeMap point-op wrappers.
//   - this file                    — `State` thread_local +
//                                    `#[init]` / `#[query]` / `#[update]`
//                                    entry points + tests.
//
// Build modes:
//   cargo build              — wasm canister artifact.
//   cargo test               — runs the 6 logic tests.
//   cargo verus verify --target wasm32-unknown-unknown
//                            — verifies the core arithmetic, conservation
//                              lemmas, and the verified runtime helpers.

pub mod core;
pub mod ic_axioms;
pub mod verified_helpers;

use candid::{CandidType, Principal};
use ic_cdk_macros::{init, query, update};
use serde::Deserialize;
use std::cell::RefCell;
use std::collections::BTreeMap;

use crate::verified_helpers::{
    verified_approve, verified_burn, verified_decrease_allowance,
    verified_increase_allowance, verified_mint, verified_transfer,
    verified_transfer_from, verified_update_minter,
};

#[derive(Default, CandidType, Deserialize)]
pub struct State {
    pub total_supply: u128,
    pub balances:     BTreeMap<Principal, u128>,
    pub allowances:   BTreeMap<(Principal, Principal), u128>,
    pub minter:       Option<Principal>,
}

thread_local! { static STATE: RefCell<State> = RefCell::new(State::default()); }

// TransferError + the generic balance helpers live in `verus_fungible_core`.
pub use verus_fungible_core::TransferError;


fn err_to_string(e: TransferError) -> String {
    match e {
        TransferError::SelfTransfer          => "self-transfer".into(),
        TransferError::Insufficient          => "insufficient balance".into(),
        TransferError::Overflow              => "balance overflow".into(),
        TransferError::InsufficientAllowance => "insufficient allowance".into(),
        TransferError::InsufficientSupply    => "insufficient supply".into(),
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
