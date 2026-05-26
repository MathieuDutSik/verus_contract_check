// Axiomatization of the Gear runtime calls we depend on.
//
// Gear's contract model is actor-style: each contract is a "program" that
// receives messages, processes them in `handle`, and emits replies. State
// is held in a `static mut` between calls (we don't model that here —
// the verified helpers operate on the `Fungible` struct directly).
//
// What we axiomatize:
//   - `ActorId` external type
//   - `msg::source()` (returns sender's ActorId; ghost `the_sender()`)
//   - `msg::reply()` — modelled as a no-op for spec purposes (it has a
//     real chain effect but doesn't change our `Fungible` view)

use vstd::prelude::*;
use gstd::ActorId;

verus! {

// ActorId is opaque (a 32-byte identifier internally).
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExActorId(#[allow(dead_code)] ActorId);

// Equality on ActorId.
pub assume_specification
    [ <ActorId as core::cmp::PartialEq>::eq ]
    (a: &ActorId, b: &ActorId) -> (r: bool)
    ensures r == (*a == *b);

/// The ghost sender of the current message. Uninterpreted; mirrors what
/// `msg::source()` returns from the Gear runtime.
pub uninterp spec fn the_sender() -> ActorId;

/// Verus-aware wrapper around `gstd::msg::source()`.
#[verifier::external_body]
pub fn source() -> (r: ActorId)
    ensures r == the_sender(),
{
    gstd::msg::source()
}

} // verus!
