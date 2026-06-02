// Axiomatization of the ink! runtime types the vesting contract uses.
//
// The chain-axiom surface for ink! is small: caller and time are
// method parameters (read inside the contract method via
// `Self::env().caller()` and `Self::env().block_timestamp()`), not
// free functions, so there are no `the_caller()` / `the_now()` ghosts.
// We only need:
//   - `ExAccountId` external type spec.
//   - PartialEq spec on `AccountId` so the verified helper can
//     compare caller against beneficiary.
//
// TRUST: every line below this banner enlarges the TCB.

use ink::primitives::AccountId;
use vstd::prelude::*;

verus! {
    // ink's AccountId is `pub struct AccountId(pub [u8; 32])` —
    // axiomatised here so we can compare caller and beneficiary in the
    // verified helper. Adding the spec is straightforward: the type
    // wraps an array, no transitive generic types to worry about.
    #[verifier::external_type_specification]
    #[verifier::external_body]
    pub struct ExAccountId(#[allow(dead_code)] AccountId);

    pub assume_specification
        [ <AccountId as ::core::cmp::PartialEq>::eq ]
        (a: &AccountId, b: &AccountId) -> (r: bool)
        ensures r == (*a == *b);
}
