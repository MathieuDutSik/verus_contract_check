// NEAR fungible-token contract with Verus-verified core arithmetic.
//
// The contract below is ordinary NEAR. The substantive transfer logic
// — caller authentication, self-transfer rejection, and the balance
// update — lives in `verified_helpers.rs` as `verified_transfer`; the
// contract method `Fungible::transfer` is a one-line forwarder.
//
// Layout (mirrors `linera_alternate` fungible):
//   - `pub mod core;`                — chain-agnostic verified core.
//   - `pub mod lookup_map_axioms;`   — NEAR `LookupMap` storage axioms
//                                      via the `AxLookupMap` wrapper.
//   - `pub mod verified_helpers;`    — `verified_transfer` /
//                                      `apply_transfer` kernels +
//                                      `the_caller()` ghost +
//                                      `predecessor()` / `panic_str()`
//                                      runtime wrappers.
//   - this file                      — `Fungible` struct, `#[near] impl`
//                                      forwarders, tests.
//
// Build modes:
//   cargo build                                       — wasm deploy artifact.
//   cargo test --target $HOST_TRIPLE                  — runs the 6 tests.
//   cargo verus verify --target wasm32-unknown-unknown — verifies `core`
//                                                       + verified_helpers.

pub mod core;
pub mod lookup_map_axioms;
pub mod verified_helpers;

use crate::lookup_map_axioms::AxLookupMap;
use crate::verified_helpers::verified_transfer;
use near_sdk::{near, AccountId, BorshStorageKey, PanicOnDefault};

#[derive(BorshStorageKey)]
#[near(serializers = [borsh])]
enum StorageKey { Balances }

#[near(contract_state)]
#[derive(PanicOnDefault)]
pub struct Fungible {
    total_supply: u128,
    balances: AxLookupMap<AccountId, u128>,
}

#[near]
impl Fungible {
    #[init]
    pub fn new(owner: AccountId, total_supply: u128) -> Self {
        let mut balances = AxLookupMap::new(StorageKey::Balances);
        balances.insert(owner, total_supply);
        Self { total_supply, balances }
    }

    pub fn balance_of(&self, account: AccountId) -> u128 {
        self.balances.get(&account).unwrap_or(0)
    }

    pub fn total_supply(&self) -> u128 { self.total_supply }

    pub fn transfer(&mut self, receiver: AccountId, amount: u128) {
        // One-line forwarder. `verified_transfer` handles caller
        // resolution, self-transfer rejection, and the balance update;
        // its `ensures` proves the full transfer semantics.
        verified_transfer(&mut self.balances, receiver, amount);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use near_sdk::test_utils::VMContextBuilder;
    use near_sdk::testing_env;

    fn acct(s: &str) -> AccountId { s.parse().unwrap() }

    fn setup(owner: &AccountId, supply: u128) -> Fungible {
        let mut ctx = VMContextBuilder::new();
        ctx.predecessor_account_id(owner.clone());
        testing_env!(ctx.build());
        Fungible::new(owner.clone(), supply)
    }

    fn set_caller(who: &AccountId) {
        let mut ctx = VMContextBuilder::new();
        ctx.predecessor_account_id(who.clone());
        testing_env!(ctx.build());
    }

    #[test]
    fn init_supply_credited_to_owner() {
        let owner = acct("owner.near");
        let f = setup(&owner, 1_000);
        assert_eq!(f.total_supply(), 1_000);
        assert_eq!(f.balance_of(owner), 1_000);
    }

    #[test]
    fn balance_of_unknown_is_zero() {
        let owner = acct("owner.near");
        let f = setup(&owner, 1_000);
        assert_eq!(f.balance_of(acct("stranger.near")), 0);
    }

    #[test]
    fn transfer_happy_path() {
        let owner = acct("owner.near");
        let alice = acct("alice.near");
        let mut f = setup(&owner, 1_000);
        set_caller(&owner);
        f.transfer(alice.clone(), 250);
        assert_eq!(f.balance_of(owner), 750);
        assert_eq!(f.balance_of(alice), 250);
    }

    #[test]
    #[should_panic(expected = "insufficient balance")]
    fn transfer_insufficient_balance() {
        let owner = acct("owner.near");
        let mut f = setup(&owner, 100);
        set_caller(&owner);
        f.transfer(acct("alice.near"), 200);
    }

    #[test]
    #[should_panic(expected = "self-transfer")]
    fn self_transfer_rejected() {
        let owner = acct("owner.near");
        let mut f = setup(&owner, 1_000);
        set_caller(&owner);
        f.transfer(owner.clone(), 10);
    }

    #[test]
    fn total_supply_invariant_after_transfer() {
        let owner = acct("owner.near");
        let alice = acct("alice.near");
        let bob   = acct("bob.near");
        let mut f = setup(&owner, 1_000);
        set_caller(&owner);
        for amt in [100u128, 200, 50] {
            f.transfer(alice.clone(), amt);
        }
        let sum = f.balance_of(owner) + f.balance_of(alice) + f.balance_of(bob);
        assert_eq!(sum, f.total_supply());
    }
}
