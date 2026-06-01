// Axiomatization of the Linera (alternate sync SDK) runtime types the
// vesting contract uses.
//
// The fungible alternate contract axiomatised `Amount`, `AccountOwner`,
// `OwnerSpender`, and `SyncMapView` (storage map). For vesting we
// don't need:
//   - `OwnerSpender` (no allowance machinery)
//   - `SyncMapView`  (one grant — no map of accounts)
//
// We do need:
//   - `AccountOwner` (the beneficiary's identity, for auth)
//   - new for vesting: `the_caller()` ghost + `caller_of` wrapper
//     (Linera's `runtime.authenticated_signer()` returns
//     `Option<AccountOwner>` — see comment on `caller_of` below)
//   - new for vesting: `the_now_micros()` ghost + `now_micros_of`
//     wrapper around the runtime's `system_time()` (returns a
//     microsecond-resolution `Timestamp`).
//
// We *don't* axiomatize `Amount` here — the verified helper operates
// on plain `u128`, matching the shared core. The unverified Contract
// glue converts `Amount` ↔ `u128` at the boundary.
//
// TRUST: every line below this banner enlarges the TCB.

use vstd::prelude::*;
use linera_sdk::linera_base_types::AccountOwner;

verus! {

// -- AccountOwner -------------------------------------------------------

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExAccountOwner(#[allow(dead_code)] AccountOwner);

// Equality on AccountOwner — bit-pattern compare under the hood.
pub assume_specification
    [ <AccountOwner as core::cmp::PartialEq>::eq ]
    (a: &AccountOwner, b: &AccountOwner) -> (r: bool)
    ensures r == (*a == *b);

// -- Caller + time ghosts ---------------------------------------------
//
// Linera's `Contract::Runtime` exposes:
//   - `authenticated_signer() -> Option<AccountOwner>`
//   - `system_time() -> Timestamp`  (microseconds since unix epoch)
//
// Both are method calls on the contract's runtime handle, accessible
// from any verified method. Modelled here as constants-within-a-
// session via uninterpreted ghosts, same idiom as NEAR/IC.

/// The ghost authenticated signer of the current operation. The
/// Linera runtime returns `Option<AccountOwner>` (because not every
/// message has a signer); for the vesting contract we require the
/// caller to be the beneficiary, so `Some(_)` is the only path that
/// progresses.
pub uninterp spec fn the_caller() -> Option<AccountOwner>;

/// The ghost wall-clock time in microseconds since the unix epoch.
/// Linera's `Timestamp` is a u64 microsecond count; the schedule
/// parameters downstream are in microseconds too.
pub uninterp spec fn the_now_micros() -> u64;

} // verus!
