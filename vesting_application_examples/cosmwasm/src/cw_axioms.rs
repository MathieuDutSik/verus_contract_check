// Axiomatization of CosmWasm storage for the vesting contract.
//
// We split the vesting state across six independent `Item`s, one per
// logical field. This mirrors the fungible CosmWasm contract's pattern
// (separate `balances_view` / `supply_view` / …) and sidesteps Verus's
// lifetime-erasure issues with serde-derived structs inside `verus!{}`.
//
// Layout:
//   BENEFICIARY    : Item<Addr>     ← set at instantiate; immutable
//   START          : Item<u64>      ← set at instantiate; immutable
//   CLIFF_DURATION : Item<u64>      ← set at instantiate; immutable
//   VEST_DURATION  : Item<u64>      ← set at instantiate; immutable
//   TOTAL          : Item<Uint128>  ← set at instantiate; immutable
//   CLAIMED        : Item<Uint128>  ← set to 0 at instantiate;
//                                     bumped by every `claim`
//
// Five of the six are immutable after instantiate; the verified
// `claim` only writes `CLAIMED`. To keep the trust surface honest
// every saver lists which views it preserves.
//
// What is and isn't axiomatized:
//   axiomatized:
//     ax_<field>_load     — point read of one Item, default None
//     ax_<field>_save     — point write of one Item, plus preservation
//                           of all other views
//     ax_*_has            — has-the-item-been-written-yet test
//
//   NOT axiomatized (deliberately):
//     Range iterators, multi-key operations — not used.
//
// TRUST: every line below this banner enlarges the TCB. The axioms
// claim what these operations do; we trust cosmwasm-std +
// cw-storage-plus to actually do them.

use vstd::prelude::*;
use cosmwasm_std::{Addr, Storage, Uint128, StdError};
use cw_storage_plus::Item;

// On-chain handles. The string prefixes are the keys cw-storage-plus
// writes under; they're disjoint so the six items live independently.
pub const BENEFICIARY:    Item<Addr>    = Item::new("beneficiary");
pub const START:          Item<u64>     = Item::new("start");
pub const CLIFF_DURATION: Item<u64>     = Item::new("cliff_duration");
pub const VEST_DURATION:  Item<u64>     = Item::new("vest_duration");
pub const TOTAL:          Item<Uint128> = Item::new("total");
pub const CLAIMED:        Item<Uint128> = Item::new("claimed");

verus! {

// -- External type/trait declarations -----------------------------------

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExAddr(#[allow(dead_code)] Addr);

// Equality on Addr. `if a == b` in exec lowers to PartialEq::eq.
pub assume_specification
    [ <Addr as core::cmp::PartialEq>::eq ]
    (a: &Addr, b: &Addr) -> (r: bool)
    ensures r == (*a == *b);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExUint128(#[allow(dead_code)] Uint128);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExStdError(#[allow(dead_code)] StdError);

#[verifier::external_trait_specification]
pub trait ExStorage {
    type ExternalTraitSpecificationFor: Storage;
}

// -- Uint128 ↔ u128 bridges ---------------------------------------------
//
// CosmWasm stores amounts as `Uint128` (u128 newtype with JSON-safe
// serialisation). The verified core works in plain `u128`, so we
// axiomatise the conversion in both directions.

pub uninterp spec fn uint128_val(u: Uint128) -> u128;

#[verifier::external_body]
pub fn ax_uint128_new(v: u128) -> (r: Uint128)
    ensures uint128_val(r) == v,
{
    Uint128::new(v)
}

#[verifier::external_body]
pub fn ax_uint128_u128(u: &Uint128) -> (r: u128)
    ensures r == uint128_val(*u),
{
    u.u128()
}

// -- Ghost projections of storage ---------------------------------------
//
// Each is `Option<T>` so we can distinguish pre-instantiate ("nothing
// stored") from post-instantiate ("value V stored").

pub uninterp spec fn beneficiary_view<S: Storage>(s: &S) -> Option<Addr>;
pub uninterp spec fn start_view<S: Storage>(s: &S)       -> Option<u64>;
pub uninterp spec fn cliff_view<S: Storage>(s: &S)       -> Option<u64>;
pub uninterp spec fn vest_view<S: Storage>(s: &S)        -> Option<u64>;
pub uninterp spec fn total_view<S: Storage>(s: &S)       -> Option<u128>;
pub uninterp spec fn claimed_view<S: Storage>(s: &S)     -> Option<u128>;

// -- Has-it-been-written? checks ---------------------------------------

#[verifier::external_body]
pub fn ax_has_beneficiary<S: Storage>(s: &S) -> (r: bool)
    ensures r == beneficiary_view(s).is_some(),
{
    BENEFICIARY.may_load(s).unwrap().is_some()
}

// -- Reads --------------------------------------------------------------

#[verifier::external_body]
pub fn ax_beneficiary_load<S: Storage>(s: &S) -> (r: Addr)
    requires beneficiary_view(s).is_some(),
    ensures  beneficiary_view(s) == Some(r),
{
    BENEFICIARY.load(s).unwrap()
}

#[verifier::external_body]
pub fn ax_start_load<S: Storage>(s: &S) -> (r: u64)
    requires start_view(s).is_some(),
    ensures  start_view(s) == Some(r),
{
    START.load(s).unwrap()
}

#[verifier::external_body]
pub fn ax_cliff_load<S: Storage>(s: &S) -> (r: u64)
    requires cliff_view(s).is_some(),
    ensures  cliff_view(s) == Some(r),
{
    CLIFF_DURATION.load(s).unwrap()
}

#[verifier::external_body]
pub fn ax_vest_load<S: Storage>(s: &S) -> (r: u64)
    requires vest_view(s).is_some(),
    ensures  vest_view(s) == Some(r),
{
    VEST_DURATION.load(s).unwrap()
}

#[verifier::external_body]
pub fn ax_total_load<S: Storage>(s: &S) -> (r: u128)
    requires total_view(s).is_some(),
    ensures  total_view(s) == Some(r),
{
    TOTAL.load(s).unwrap().u128()
}

#[verifier::external_body]
pub fn ax_claimed_load<S: Storage>(s: &S) -> (r: u128)
    requires claimed_view(s).is_some(),
    ensures  claimed_view(s) == Some(r),
{
    CLAIMED.load(s).unwrap().u128()
}

// -- Writes -------------------------------------------------------------
//
// Each save sets its own view and preserves all five other views.
// The verified `claim` only calls `ax_claimed_save`; the other five
// fire only during `verified_instantiate`.

#[verifier::external_body]
pub fn ax_beneficiary_save<S: Storage>(s: &mut S, v: &Addr)
    ensures
        beneficiary_view(final(s)) == Some(*v),
        start_view(final(s))       == start_view(old(s)),
        cliff_view(final(s))       == cliff_view(old(s)),
        vest_view(final(s))        == vest_view(old(s)),
        total_view(final(s))       == total_view(old(s)),
        claimed_view(final(s))     == claimed_view(old(s)),
{
    BENEFICIARY.save(s, v).unwrap()
}

#[verifier::external_body]
pub fn ax_start_save<S: Storage>(s: &mut S, v: u64)
    ensures
        start_view(final(s))       == Some(v),
        beneficiary_view(final(s)) == beneficiary_view(old(s)),
        cliff_view(final(s))       == cliff_view(old(s)),
        vest_view(final(s))        == vest_view(old(s)),
        total_view(final(s))       == total_view(old(s)),
        claimed_view(final(s))     == claimed_view(old(s)),
{
    START.save(s, &v).unwrap()
}

#[verifier::external_body]
pub fn ax_cliff_save<S: Storage>(s: &mut S, v: u64)
    ensures
        cliff_view(final(s))       == Some(v),
        beneficiary_view(final(s)) == beneficiary_view(old(s)),
        start_view(final(s))       == start_view(old(s)),
        vest_view(final(s))        == vest_view(old(s)),
        total_view(final(s))       == total_view(old(s)),
        claimed_view(final(s))     == claimed_view(old(s)),
{
    CLIFF_DURATION.save(s, &v).unwrap()
}

#[verifier::external_body]
pub fn ax_vest_save<S: Storage>(s: &mut S, v: u64)
    ensures
        vest_view(final(s))        == Some(v),
        beneficiary_view(final(s)) == beneficiary_view(old(s)),
        start_view(final(s))       == start_view(old(s)),
        cliff_view(final(s))       == cliff_view(old(s)),
        total_view(final(s))       == total_view(old(s)),
        claimed_view(final(s))     == claimed_view(old(s)),
{
    VEST_DURATION.save(s, &v).unwrap()
}

#[verifier::external_body]
pub fn ax_total_save<S: Storage>(s: &mut S, v: u128)
    ensures
        total_view(final(s))       == Some(v),
        beneficiary_view(final(s)) == beneficiary_view(old(s)),
        start_view(final(s))       == start_view(old(s)),
        cliff_view(final(s))       == cliff_view(old(s)),
        vest_view(final(s))        == vest_view(old(s)),
        claimed_view(final(s))     == claimed_view(old(s)),
{
    TOTAL.save(s, &Uint128::new(v)).unwrap()
}

#[verifier::external_body]
pub fn ax_claimed_save<S: Storage>(s: &mut S, v: u128)
    ensures
        claimed_view(final(s))     == Some(v),
        beneficiary_view(final(s)) == beneficiary_view(old(s)),
        start_view(final(s))       == start_view(old(s)),
        cliff_view(final(s))       == cliff_view(old(s)),
        vest_view(final(s))        == vest_view(old(s)),
        total_view(final(s))       == total_view(old(s)),
{
    CLAIMED.save(s, &Uint128::new(v)).unwrap()
}

} // verus!
