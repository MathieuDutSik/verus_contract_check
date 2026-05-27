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
//     SyncContext external_trait_specification (super-trait: Clone, via the
//       proxy-trait-with-external-supertraits pattern that the multiversx
//       BigUint axiomatization established)
//     SyncMapView external_type_specification (specialized to the concrete
//       SyncViewStorageContext from linera_sdk's type alias)
//     account_map_view / allowance_map_view  ghost projections
//     ax_account_get / ax_account_insert / ax_account_remove  point-op
//       wrappers specialized to (AccountOwner, Amount). Skips Borrow<Q>
//       generality — the contract only uses Q = I.
//
// TRUST: every line below this banner enlarges the TCB. We trust the
// linera SDK to implement these operations as the axioms claim.

use vstd::prelude::*;
use linera_sdk::linera_base_types::{Amount, AccountOwner, OwnerSpender};
use linera_sdk::views::{linera_views, SyncMapView};
use linera_sdk::KeyValueStore;
use linera_views::sync_views::context::SyncViewContext;
use linera_views::sync_views::map_view::SyncMapView as SyncMapViewBase;
#[cfg(verus_only)]
use vstd::map::Map as SpecMap;

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

// -- SyncViewContext + SyncMapView (the underlying generic types) ------
//
// `linera_sdk::views::SyncMapView<K, V>` is a 2-param alias for
// `linera_views::SyncMapView<SyncViewStorageContext, K, V>`, and
// `SyncViewStorageContext` is itself an alias for `SyncViewContext<(), KeyValueStore>`.
// Verus's external_type_specification operates on the *underlying* struct
// definitions, so we declare proxies with matching generic signatures.
//
// We don't axiomatize `SyncContext` as a trait — our wrapper functions
// below are specialized to the SDK's 2-param alias, so the M parameter
// (and its SyncContext bound) never appears in any verified signature.

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExKeyValueStore(#[allow(dead_code)] KeyValueStore);

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::accept_recursive_types(E)]
#[verifier::accept_recursive_types(S)]
pub struct ExSyncViewContext<E, S>(#[allow(dead_code)] SyncViewContext<E, S>);

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::accept_recursive_types(C)]
#[verifier::accept_recursive_types(K)]
#[verifier::accept_recursive_types(V)]
pub struct ExSyncMapView<C, K, V>(#[allow(dead_code)] SyncMapViewBase<C, K, V>);

/// Ghost projection of the `accounts` map into a SpecMap.
pub uninterp spec fn account_map_view(m: &SyncMapView<AccountOwner, Amount>) -> SpecMap<AccountOwner, Amount>;

/// Ghost projection of the `allowances` map into a SpecMap.
pub uninterp spec fn allowance_map_view(m: &SyncMapView<OwnerSpender, Amount>) -> SpecMap<OwnerSpender, Amount>;

// -- Account-map point-op wrappers -------------------------------------
//
// Specialized to (K = AccountOwner, V = Amount). Skip Borrow<Q> generality:
// the contract only ever looks up by `&AccountOwner`, never by a borrowed
// shorter form. Errors at the storage layer are not modelled — the
// runtime wrappers `.expect()` them, matching state.rs's current behavior.

#[verifier::external_body]
pub fn ax_account_get(m: &SyncMapView<AccountOwner, Amount>, k: &AccountOwner) -> (r: Option<Amount>)
    ensures
        r == if account_map_view(m).dom().contains(*k) {
            Some(account_map_view(m)[*k])
        } else {
            None
        },
{
    m.get(k).expect("ax_account_get failed")
}

#[verifier::external_body]
pub fn ax_account_insert(m: &mut SyncMapView<AccountOwner, Amount>, k: &AccountOwner, v: Amount)
    ensures
        account_map_view(final(m)) == account_map_view(old(m)).insert(*k, v),
{
    m.insert(k, v).expect("ax_account_insert failed");
}

#[verifier::external_body]
pub fn ax_account_remove(m: &mut SyncMapView<AccountOwner, Amount>, k: &AccountOwner)
    ensures
        account_map_view(final(m)) == account_map_view(old(m)).remove(*k),
{
    m.remove(k).expect("ax_account_remove failed");
}

// -- Allowance-map point-op wrappers -----------------------------------
// Same pattern as the account map, specialized to (OwnerSpender, Amount).

#[verifier::external_body]
pub fn ax_allowance_get(m: &SyncMapView<OwnerSpender, Amount>, k: &OwnerSpender) -> (r: Option<Amount>)
    ensures
        r == if allowance_map_view(m).dom().contains(*k) {
            Some(allowance_map_view(m)[*k])
        } else {
            None
        },
{
    m.get(k).expect("ax_allowance_get failed")
}

#[verifier::external_body]
pub fn ax_allowance_insert(m: &mut SyncMapView<OwnerSpender, Amount>, k: &OwnerSpender, v: Amount)
    ensures
        allowance_map_view(final(m)) == allowance_map_view(old(m)).insert(*k, v),
{
    m.insert(k, v).expect("ax_allowance_insert failed");
}

#[verifier::external_body]
pub fn ax_allowance_remove(m: &mut SyncMapView<OwnerSpender, Amount>, k: &OwnerSpender)
    ensures
        allowance_map_view(final(m)) == allowance_map_view(old(m)).remove(*k),
{
    m.remove(k).expect("ax_allowance_remove failed");
}

} // verus!
