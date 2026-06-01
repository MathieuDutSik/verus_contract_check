// Axiomatization of the Gear runtime calls the vesting contract uses.
//
// New for vesting versus the fungible Gear contract:
//   - `exec::block_timestamp()` wrapper + `the_now_ms()` ghost.
//
// Reused unchanged from the fungible:
//   - ExActorId external type spec
//   - PartialEq spec for ActorId
//   - `msg::source()` wrapper + `the_sender()` ghost
//
// TRUST: every line below this banner enlarges the TCB.

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

/// The ghost sender of the current message. Mirrors `msg::source()`.
pub uninterp spec fn the_sender() -> ActorId;

/// The ghost wall-clock time in milliseconds since the unix epoch.
/// Mirrors `exec::block_timestamp()`. Constant across a single
/// message-handle invocation; the Gear runtime pins it to the block's
/// timestamp at message-dispatch time.
pub uninterp spec fn the_now_ms() -> u64;

/// Verus-aware wrapper around `gstd::msg::source()`.
#[verifier::external_body]
pub fn source() -> (r: ActorId)
    ensures r == the_sender(),
{
    gstd::msg::source()
}

/// Verus-aware wrapper around `gstd::exec::block_timestamp()`.
#[verifier::external_body]
pub fn now_ms() -> (r: u64)
    ensures r == the_now_ms(),
{
    gstd::exec::block_timestamp()
}

} // verus!
