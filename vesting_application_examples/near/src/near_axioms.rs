// Axiomatization of NEAR's per-method runtime calls that the vesting
// contract needs:
//
//   - `env::predecessor_account_id()`  — who called this method
//   - `env::block_timestamp_ms()`      — current wall-clock time in ms
//   - `env::panic_str(msg)`            — never-returns failure
//
// Each runtime call is wrapped in a Verus-aware function whose `ensures`
// ties the return value to an *uninterpreted ghost spec function*
// (`the_caller()`, `the_now()`). Within one verification session the
// spec function is constant — calling the wrapper twice in the same
// method yields the same value, which is what the runtime guarantees.
//
// `AccountId` is reused via an `external_type_specification` (same
// shape as the fungible example). For the vesting contract we don't
// need to axiomatize `LookupMap` — a single `Grant` lives directly in
// the `#[near(contract_state)]` struct, so storage is just field access
// on `&mut self` that the SDK macro generates.
//
// TRUST: everything below this banner enlarges the TCB. The axioms
// claim what the wrapped NEAR runtime calls do; we trust the SDK to
// actually do it.

use vstd::prelude::*;
use near_sdk::{env, AccountId};

verus! {

// NEAR's account identifier. Opaque to Verus; we use it only as the
// beneficiary field's type.
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExAccountId(#[allow(dead_code)] AccountId);

// Equality on AccountId. `if a == b` in exec code lowers to a
// `PartialEq::eq` call; this spec lets Verus reason about it.
pub assume_specification
    [ <AccountId as core::cmp::PartialEq>::eq ]
    (a: &AccountId, b: &AccountId) -> (r: bool)
    ensures r == (*a == *b);

/// The ghost caller of the current contract method. Uninterpreted; it
/// stands for whatever AccountId the NEAR runtime says called us.
/// `predecessor()` (below) is wired to return this value, and every
/// downstream proof reasons in terms of `the_caller()`.
pub uninterp spec fn the_caller() -> AccountId;

/// The ghost wall-clock time of the current contract method, in
/// milliseconds since the unix epoch. Uninterpreted, but constant
/// across the verification session — same idiom as `the_caller()`.
///
/// NEAR's `env::block_timestamp_ms()` is constant within a single
/// method execution: it's pinned to the block's timestamp, which is
/// fixed at block-production time. So calling `now_ms()` twice in a
/// single verified method body yields the same Verus value, matching
/// the runtime.
pub uninterp spec fn the_now() -> u64;

/// Verus-aware wrapper around `env::predecessor_account_id()`. Its
/// `ensures` makes the return value equal to the ghost `the_caller()`.
#[verifier::external_body]
pub fn predecessor() -> (r: AccountId)
    ensures r == the_caller(),
{
    env::predecessor_account_id()
}

/// Verus-aware wrapper around `env::block_timestamp_ms()`. Returns the
/// ghost `the_now()`. The NEAR runtime returns a non-zero monotonic
/// timestamp; we *don't* axiomatize monotonicity across the wrapper
/// because each verified method only ever observes one timestamp — the
/// cross-block monotonicity is an external trace property, not a
/// per-method invariant.
#[verifier::external_body]
pub fn now_ms() -> (r: u64)
    ensures r == the_now(),
{
    env::block_timestamp_ms()
}

/// Panic with `msg`; never returns. Wraps `env::panic_str`. The
/// `ensures false` postcondition models divergence — any caller will
/// have its goal "vacuously satisfied" on the panicking branch.
#[verifier::external_body]
pub fn panic_str(msg: &'static str)
    ensures false,
{
    env::panic_str(msg)
}

} // verus!
