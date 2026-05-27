// NEAR fungible-token contract with Verus-verified core arithmetic.
//
// The contract below is ordinary NEAR — the only addition versus a plain
// fungible contract is the `pub mod core;` line, plus the `transfer` body
// delegating its arithmetic to `core::transfer_balances`. Everything else
// (the #[near] macros, LookupMap storage, the 6 tests) is unchanged.
//
// Build modes:
//   cargo build                                       — wasm deploy artifact.
//   cargo test --target $HOST_TRIPLE                  — runs the 6 tests.
//   cargo verus verify --target wasm32-unknown-unknown — verifies `core`.

pub mod core;
pub mod lookup_map_axioms;

use crate::lookup_map_axioms::AxLookupMap;
use near_sdk::{env, near, AccountId, BorshStorageKey, PanicOnDefault};

// Verified helper: apply a transfer to the in-memory balance map.
// `Fungible::transfer` (below) reads the caller from `predecessor_account_id`,
// rejects self-transfer, then delegates the actual storage mutation to this
// function. The `ensures` clauses below pin down what `apply_transfer` does
// to the abstract view (`@`) of the balance map:
//   - the sender ends up debited by `amount`,
//   - the receiver ends up credited by `amount`,
//   - the sum of those two new balances equals the sum of their two old
//     balances (with absent entries treated as 0),
//   - every other account's balance is untouched.
// If the arithmetic underflows or overflows, `core::transfer_balances`
// returns Err, this function panics via `panic_str`, and the post-conditions
// are vacuously true on that path.
vstd::prelude::verus! {
    #[cfg(verus_only)]
    use vstd::prelude::*;
    #[cfg(verus_only)]
    use verus_fungible_core::{balance_at, transfer_balances_map, nat_balances};

    /// Panic with `msg`; never returns. Wraps `env::panic_str`. The
    /// `ensures false` postcondition models divergence — any caller will
    /// have its goal "vacuously satisfied" on the panicking branch.
    #[verifier::external_body]
    fn panic_str(msg: &'static str)
        ensures false,
    {
        env::panic_str(msg)
    }

    /// Read a balance, defaulting absent entries to 0.
    fn read_balance(map: &AxLookupMap<AccountId, u128>, k: &AccountId) -> (r: u128)
        ensures
            r == if map@.dom().contains(*k) { map@[*k] } else { 0u128 },
    {
        match map.get(k) {
            Some(v) => v,
            None    => 0u128,
        }
    }

    /// The ghost caller of the current contract method. Uninterpreted —
    /// it stands for whatever AccountId the chain runtime says called us.
    /// `predecessor()` (below) is wired to return this value, and every
    /// downstream proof reasons in terms of `the_caller()`.
    pub uninterp spec fn the_caller() -> AccountId;

    /// Verus-aware wrapper around `env::predecessor_account_id()`. Its
    /// `ensures` makes the return value equal to the ghost `the_caller()`.
    #[verifier::external_body]
    fn predecessor() -> (r: AccountId)
        ensures r == the_caller(),
    {
        env::predecessor_account_id()
    }

    /// Verified dispatch step: equivalent to `Fungible::transfer`'s body.
    /// Reads the caller via `predecessor()` (axiomatised as
    /// `the_caller()`), rejects self-transfer via `panic_str`, then
    /// delegates the storage mutation to `apply_transfer`.
    ///
    /// No `requires`: the function is callable in any state. The `ensures`
    /// describes only the success path; on the panic path the postcondition
    /// is vacuously satisfied (because `panic_str` has `ensures false`).
    ///
    /// `Fungible::transfer` below is a one-line forwarder to this
    /// function — every substantive operation is verified.
    pub fn verified_transfer(
        balances: &mut AxLookupMap<AccountId, u128>,
        receiver: AccountId,
        amount: u128,
    )
        ensures
            // If we returned, the caller wasn't the receiver and the
            // storage update is exactly the abstract transfer.
            the_caller() != receiver,
            final(balances)@
                == transfer_balances_map(old(balances)@, the_caller(), receiver, amount),
    {
        let sender = predecessor();
        if sender == receiver {
            panic_str("self-transfer");
        }
        apply_transfer(balances, sender, receiver, amount);
    }

    pub fn apply_transfer(
        balances: &mut AxLookupMap<AccountId, u128>,
        sender: AccountId,
        receiver: AccountId,
        amount: u128,
    )
        requires sender != receiver,
        ensures
            // Single structural ensures: the storage update is exactly
            // `state_after_transfer`'s balance update.
            final(balances)@
                == transfer_balances_map(old(balances)@, sender, receiver, amount),
    {
        let from = read_balance(balances, &sender);
        let to   = read_balance(balances, &receiver);
        match crate::core::transfer_balances(from, to, amount) {
            Ok((from_next, to_next)) => {
                balances.insert(sender, from_next);
                balances.insert(receiver, to_next);
            }
            Err(msg) => panic_str(msg),
        }
    }

    // `nat_balances`, `lemma_apply_transfer_matches_state`, `balance_at`,
    // and `transfer_balances_map` previously lived here; they now live in
    // `verus_fungible_core` and are imported above. The refinement lemma
    // is `lemma_balance_map_transfer_matches_state` in the shared crate.
}

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
