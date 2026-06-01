// Axiomatization of the IC runtime calls the vesting contract uses.
//
// IC's surface is small:
//   - State lives in-process (`thread_local! RefCell<State>`); no
//     external storage trait to axiomatise.
//   - `Principal` is the address-like type; opaque to Verus and used
//     only for equality + value passing.
//   - `ic_cdk::api::caller()` is a free function; wrapped here with
//     a `the_caller()` ghost — same idiom as NEAR's `predecessor()`.
//   - `ic_cdk::api::time()` is also a free function returning ns since
//     the unix epoch as u64; wrapped here with a `the_now_ns()` ghost
//     — new to vesting (the fungible contract had no time concern).
//
// Both ghosts are constant within a single verification session: the
// IC runtime pins the message's caller and the block's timestamp at
// dispatch time, so calling the wrapped function twice in one verified
// method body yields the same Verus value, matching the runtime.
//
// TRUST: every line below this banner enlarges the TCB.

use vstd::prelude::*;
use candid::Principal;

verus! {

// Principal is opaque; we use it only as the beneficiary's identity.
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExPrincipal(#[allow(dead_code)] Principal);

// Equality on Principal — required for `if caller == beneficiary`.
pub assume_specification
    [ <Principal as core::cmp::PartialEq>::eq ]
    (a: &Principal, b: &Principal) -> (r: bool)
    ensures r == (*a == *b);

/// The ghost caller of the current method. Uninterpreted; stands for
/// whatever Principal the IC says called us.
pub uninterp spec fn the_caller() -> Principal;

/// The ghost wall-clock time in nanoseconds since the unix epoch.
/// Uninterpreted and constant across the session, mirroring how IC
/// pins `ic_cdk::api::time()` to the block timestamp at dispatch.
pub uninterp spec fn the_now_ns() -> u64;

/// Verus-aware wrapper around `ic_cdk::api::caller()`. Returns the
/// ghost `the_caller()`.
#[verifier::external_body]
pub fn caller() -> (r: Principal)
    ensures r == the_caller(),
{
    ic_cdk::api::caller()
}

/// Verus-aware wrapper around `ic_cdk::api::time()`. Returns the ghost
/// `the_now_ns()` — nanoseconds since the unix epoch.
#[verifier::external_body]
pub fn now_ns() -> (r: u64)
    ensures r == the_now_ns(),
{
    ic_cdk::api::time()
}

/// Panic with `msg`; never returns. Models `ic_cdk::trap`.
#[verifier::external_body]
pub fn trap(msg: &str)
    ensures false,
{
    ic_cdk::trap(msg)
}

} // verus!
