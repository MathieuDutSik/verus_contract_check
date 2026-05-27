// Axiomatization of the linera_alternate runtime types we depend on.
//
// What is and isn't axiomatized:
//
//   axiomatized here:
//     Amount external_type_specification + ghost `amount_val(a) -> u128`
//     Amount::ZERO  (= 0u128 under amount_val)
//     Amount equality (via PartialEq::eq)
//     Amount::saturating_add_assign  (saturates at u128::MAX)
//     Amount::try_sub_assign          (Result-returning, underflow caught)
//     u128::from(Amount)              (the inner value)
//     AccountOwner / OwnerSpender external_type_specifications (opaque)
//     OwnerSpender::new(owner, spender) (constructor: stores both fields)
//
//   NOT axiomatized (deferred):
//     SyncMapView<C, I, V> + its get/insert/remove/get_mut_or_default
//     (each is a substantial axiomatization piece: ~80 LOC + a ghost
//     SpecMap projection. Tracked in TODO.md.)
//
// TRUST: every line below this banner enlarges the TCB. We trust the
// linera SDK to implement these operations as the axioms claim.

use vstd::prelude::*;
use linera_sdk::linera_base_types::{Amount, AccountOwner, OwnerSpender};

verus! {

// -- Amount --------------------------------------------------------------

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExAmount(#[allow(dead_code)] Amount);

/// Ghost projection: the u128 value carried by an `Amount`.
pub uninterp spec fn amount_val(a: Amount) -> u128;

// Equality on Amount: lowers to PartialEq::eq at exec time. The two
// Amounts are equal iff their u128 values are equal.
pub assume_specification
    [ <Amount as core::cmp::PartialEq>::eq ]
    (a: &Amount, b: &Amount) -> (r: bool)
    ensures r == (amount_val(*a) == amount_val(*b));

// `Amount::ZERO` — the constant zero amount. We can't `assume_specification`
// a const directly, so we expose a wrapper Verus can reason about.
#[verifier::external_body]
pub fn amount_zero() -> (r: Amount)
    ensures amount_val(r) == 0u128,
{
    Amount::ZERO
}

/// Saturating in-place addition. Linera's `saturating_add_assign` saturates
/// at `u128::MAX` rather than failing on overflow. Honest axiomatization:
/// the post-state's `amount_val` is the saturating sum of the two inputs.
#[verifier::external_body]
pub fn amount_saturating_add_assign(target: &mut Amount, other: Amount)
    ensures
        amount_val(*final(target)) ==
            if amount_val(*old(target)) as int + amount_val(other) as int <= u128::MAX as int {
                (amount_val(*old(target)) + amount_val(other)) as u128
            } else {
                u128::MAX
            },
{
    target.saturating_add_assign(other);
}

/// Checked in-place subtraction. Returns Err on underflow; on Ok, the
/// post-state is `old - other`.
#[verifier::external_body]
pub fn amount_try_sub_assign(target: &mut Amount, other: Amount) -> (r: Result<(), ()>)
    ensures
        match r {
            Ok(()) =>
                amount_val(*old(target)) >= amount_val(other)
                && amount_val(*final(target))
                    == (amount_val(*old(target)) - amount_val(other)) as u128,
            Err(()) =>
                amount_val(*old(target)) < amount_val(other)
                && amount_val(*final(target)) == amount_val(*old(target)),
        },
{
    // Map linera's ArithmeticError to () so the verified spec is closed.
    target.try_sub_assign(other).map_err(|_| ())
}

/// Convert an `Amount` to its inner `u128`. Linera exposes this as
/// `u128::from(amount)` (or `.into()`). We wrap it to give Verus a
/// pinned-down `amount_val` reading.
#[verifier::external_body]
pub fn amount_to_u128(a: Amount) -> (r: u128)
    ensures r == amount_val(a),
{
    u128::from(a)
}

// -- AccountOwner -------------------------------------------------------

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExAccountOwner(#[allow(dead_code)] AccountOwner);

// Equality on AccountOwner: pure bit-pattern compare.
pub assume_specification
    [ <AccountOwner as core::cmp::PartialEq>::eq ]
    (a: &AccountOwner, b: &AccountOwner) -> (r: bool)
    ensures r == (*a == *b);

// -- OwnerSpender -------------------------------------------------------

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExOwnerSpender(#[allow(dead_code)] OwnerSpender);

pub assume_specification
    [ <OwnerSpender as core::cmp::PartialEq>::eq ]
    (a: &OwnerSpender, b: &OwnerSpender) -> (r: bool)
    ensures r == (*a == *b);

/// Ghost projection of an `OwnerSpender` into its (owner, spender) pair.
/// Uninterpreted, but the constructor below pins down the relationship.
pub uninterp spec fn owner_spender_pair(os: OwnerSpender) -> (AccountOwner, AccountOwner);

/// Constructor for OwnerSpender. Pins `owner_spender_pair` of the result.
#[verifier::external_body]
pub fn owner_spender_new(owner: AccountOwner, spender: AccountOwner) -> (r: OwnerSpender)
    ensures owner_spender_pair(r) == (owner, spender),
{
    OwnerSpender::new(owner, spender)
}

} // verus!
