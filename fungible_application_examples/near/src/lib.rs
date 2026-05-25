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
use near_sdk::{env, near, require, AccountId, BorshStorageKey, PanicOnDefault};

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

    pub fn apply_transfer(
        balances: &mut AxLookupMap<AccountId, u128>,
        sender: AccountId,
        receiver: AccountId,
        amount: u128,
    )
        requires
            old(balances).view().dom().contains(sender) ==> true,    // trivially true; just naming
            sender != receiver,
        ensures
            // Two changed entries are exactly debit/credit.
            final(balances)@.dom().contains(sender),
            final(balances)@.dom().contains(receiver),
            final(balances)@[sender]
                == (if old(balances)@.dom().contains(sender) { old(balances)@[sender] } else { 0u128 }) - amount,
            final(balances)@[receiver]
                == (if old(balances)@.dom().contains(receiver) { old(balances)@[receiver] } else { 0u128 }) + amount,
            // All other entries unchanged.
            forall|k: AccountId| #![auto] k != sender && k != receiver ==>
                final(balances)@.dom().contains(k) == old(balances)@.dom().contains(k),
            forall|k: AccountId| #![auto]
                k != sender && k != receiver && old(balances)@.dom().contains(k) ==>
                    final(balances)@[k] == old(balances)@[k],
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
        let sender = env::predecessor_account_id();
        require!(sender != receiver, "self-transfer");
        // Delegate to the Verus-verified `apply_transfer`: it reads from
        // the LookupMap via the axiomatized wrapper, calls the verified
        // `core::transfer_balances` for the arithmetic, and writes back —
        // all with `ensures` clauses proven against the AxLookupMap view.
        apply_transfer(&mut self.balances, sender, receiver, amount);
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
