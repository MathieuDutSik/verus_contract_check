// Verified kernels that `Fungible::transfer` forwards to.
//
// Same pattern as `verified_state.rs` in the linera_alternate fungible
// example: the contract's exposed method is a one-line forwarder; the
// substantive logic — caller authentication via `the_caller()`,
// self-transfer rejection, and the balance update — lives here with
// `ensures` clauses that pin the abstract effect on the `@`-projected
// view of the `AxLookupMap` balances.
//
// The `panic_str` axiom (divergence via `env::panic_str`) and the
// `predecessor` / `the_caller` ghost machinery also live here because
// they're consumed only by the verified helpers below.

use crate::lookup_map_axioms::AxLookupMap;
use near_sdk::{env, AccountId};

vstd::prelude::verus! {
    #[cfg(verus_only)]
    use vstd::prelude::*;
    #[cfg(verus_only)]
    use verus_fungible_core::{balance_at, transfer_balances_map};

    /// Panic with `msg`; never returns. Wraps `env::panic_str`. The
    /// `ensures false` postcondition models divergence — any caller will
    /// have its goal "vacuously satisfied" on the panicking branch.
    #[verifier::external_body]
    pub(crate) fn panic_str(msg: &'static str)
        ensures false,
    {
        env::panic_str(msg)
    }

    /// Read a balance, defaulting absent entries to 0.
    pub(crate) fn read_balance(map: &AxLookupMap<AccountId, u128>, k: &AccountId) -> (r: u128)
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
    pub(crate) fn predecessor() -> (r: AccountId)
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
    /// `Fungible::transfer` is a one-line forwarder to this
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
