// Axiomatization of the IC runtime calls we depend on.
//
// IC's surface is much smaller than NEAR's or CosmWasm's because:
//   - State is in-process (`thread_local! RefCell<State>`), no external
//     storage trait to axiomatize.
//   - The contract author defines the state struct directly. Verus can
//     reason about it natively (via vstd's BTreeMap specs).
//
// What we still need:
//   - external_type_specification for Principal (an opaque struct).
//   - axiomatized `caller()` wrapper that returns an uninterpreted
//     `the_caller()` ghost — mirrors NEAR's `predecessor()`.

use vstd::prelude::*;
use candid::Principal;

verus! {

// Principal is opaque; we use it only as a map key and as the caller's
// identity.
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExPrincipal(#[allow(dead_code)] Principal);

// Equality on Principal — required for `if caller == receiver`.
pub assume_specification
    [ <Principal as core::cmp::PartialEq>::eq ]
    (a: &Principal, b: &Principal) -> (r: bool)
    ensures r == (*a == *b);

/// The ghost caller of the current update method. Uninterpreted —
/// stands for whatever Principal the IC says called us.
pub uninterp spec fn the_caller() -> Principal;

/// Verus-aware wrapper around `ic_cdk::api::caller()`. Its `ensures`
/// makes the return value equal to the ghost `the_caller()`.
#[verifier::external_body]
pub fn caller() -> (r: Principal)
    ensures r == the_caller(),
{
    ic_cdk::api::caller()
}

/// Panic with `msg`; never returns. Models `ic_cdk::trap`.
#[verifier::external_body]
pub fn trap(msg: &str)
    ensures false,
{
    ic_cdk::trap(msg)
}

} // verus!
