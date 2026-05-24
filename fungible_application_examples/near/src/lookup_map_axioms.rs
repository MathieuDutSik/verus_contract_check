// Axiomatization of `near_sdk::store::LookupMap`.
//
// `LookupMap<K, V, H>` is an SDK-provided persistent key/value store that
// lives in NEAR contract storage. To reason about it in Verus, we lift
// every map to a ghost `view(&m): Map<K, V>` that abstracts away the
// storage cache, hashing, and serialisation details, and we expose each
// public method through a thin `#[verifier::external_body]` wrapper
// whose `ensures` clause describes its effect on the view.
//
// What is and isn't axiomatized here:
//
//   axiomatized:
//     lm_new          — empty view on construction
//     lm_get          — read by value (Copy values), Option<V>
//     lm_get_ref      — read by reference, Option<&V>
//     lm_insert       — point update, returns the prior Option<V>
//     lm_remove       — point delete, returns the prior Option<V>
//     lm_contains_key — membership test
//     lm_set          — Some => insert, None => remove
//     lm_flush        — write-back to storage; no semantic effect on view
//
//   NOT axiomatized (deliberately):
//     get_mut         — needs prophecy/borrow-tracking to spec a `&mut V`
//                       return; would clutter our first cut
//     entry           — entry API has a stateful return value; defer
//     with_hasher     — same view semantics as `new`, defer
//
// Why wrappers and not `assume_specification`:
//
//   `assume_specification` requires the proxy signature to match the SDK
//   method's signature exactly — including generic parameters. The Q-
//   generic read methods (`get<Q>` where `K: Borrow<Q>`) would force us
//   to introduce `borrows_to_key` / `maps_borrowed_key_to_value` helper
//   predicates over the view, like vstd does for BTreeMap. That is a
//   defensible engineering step but a substantial layer of its own.
//
//   These wrappers specialize `Q = K`, which matches all uses in this
//   crate, and give the simplest possible spec. The downside is that
//   `Fungible::transfer` must call `lm_get(&self.balances, &k)` rather
//   than `self.balances.get(&k)`. The wrapper-vs-direct-call cost is a
//   localised mechanical change; the spec semantics are identical.
//
// TRUST: every line below this banner enlarges the TCB. The axioms claim
// what `LookupMap`'s methods do; we trust the SDK to actually do it.

use vstd::prelude::*;
use vstd::map::*;
use near_sdk::store::LookupMap;
use near_sdk::store::key::{Identity, ToKey};
use near_sdk::borsh::{BorshDeserialize, BorshSerialize};
use near_sdk::IntoStorageKey;

// -- External type declarations -----------------------------------------
//
// Verus needs every external (non-Verus-aware) type that appears in spec
// or proof code to be declared via `external_type_specification`. The
// wrapper structs below name the SDK types we'll reason about.

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::accept_recursive_types(K)]
#[verifier::accept_recursive_types(V)]
#[verifier::accept_recursive_types(H)]
pub struct ExLookupMap<K: BorshSerialize + Ord, V: BorshSerialize, H: ToKey>(LookupMap<K, V, H>);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExIdentity(Identity);

verus! {

// -- Ghost projection ---------------------------------------------------

/// The abstract `Map<K, V>` content of a `LookupMap`. Uninterpreted —
/// the wrappers below are the only thing said about it.
pub uninterp spec fn view<K, V, H>(m: &LookupMap<K, V, H>) -> Map<K, V>
    where
        K: BorshSerialize + Ord,
        V: BorshSerialize,
        H: ToKey;

// -- Constructor --------------------------------------------------------

/// `LookupMap::new(prefix)` returns an empty map.
#[verifier::external_body]
pub fn lm_new<K, V, S>(prefix: S) -> (m: LookupMap<K, V>)
    where
        K: BorshSerialize + Ord,
        V: BorshSerialize + BorshDeserialize,
        S: IntoStorageKey,
    ensures
        view(&m) == Map::<K, V>::empty(),
{
    LookupMap::new(prefix)
}

// -- Reads --------------------------------------------------------------

/// Read by reference. `Some(v)` iff `k` is in the view's domain.
#[verifier::external_body]
pub fn lm_get_ref<'a, K, V, H>(m: &'a LookupMap<K, V, H>, k: &K) -> (r: Option<&'a V>)
    where
        K: BorshSerialize + Ord + Clone,
        V: BorshSerialize + BorshDeserialize,
        H: ToKey,
    ensures
        match r {
            Some(v) => view(m).dom().contains(*k) && *v == view(m)[*k],
            None    => !view(m).dom().contains(*k),
        },
{
    m.get(k)
}

/// Read by value (for `Copy` values like `u128`). Returns the contained
/// value rather than a reference, which is friendlier in arithmetic code.
#[verifier::external_body]
pub fn lm_get<K, V, H>(m: &LookupMap<K, V, H>, k: &K) -> (r: Option<V>)
    where
        K: BorshSerialize + Ord + Clone,
        V: BorshSerialize + BorshDeserialize + Copy,
        H: ToKey,
    ensures
        match r {
            Some(v) => view(m).dom().contains(*k) && v == view(m)[*k],
            None    => !view(m).dom().contains(*k),
        },
{
    m.get(k).copied()
}

/// Membership test.
#[verifier::external_body]
pub fn lm_contains_key<K, V, H>(m: &LookupMap<K, V, H>, k: &K) -> (r: bool)
    where
        K: BorshSerialize + Ord + Clone,
        V: BorshSerialize + BorshDeserialize,
        H: ToKey,
    ensures
        r == view(m).dom().contains(*k),
{
    m.contains_key(k)
}

// -- Writes -------------------------------------------------------------

/// Point insert. Returns the previous value if the key was present.
#[verifier::external_body]
pub fn lm_insert<K, V, H>(m: &mut LookupMap<K, V, H>, k: K, v: V) -> (r: Option<V>)
    where
        K: BorshSerialize + Ord + Clone,
        V: BorshSerialize + BorshDeserialize,
        H: ToKey,
    ensures
        view(final(m)) == view(old(m)).insert(k, v),
        match r {
            Some(prev) => view(old(m)).dom().contains(k) && prev == view(old(m))[k],
            None       => !view(old(m)).dom().contains(k),
        },
{
    m.insert(k, v)
}

/// Point delete. Returns the previous value if the key was present.
#[verifier::external_body]
pub fn lm_remove<K, V, H>(m: &mut LookupMap<K, V, H>, k: &K) -> (r: Option<V>)
    where
        K: BorshSerialize + Ord + Clone,
        V: BorshSerialize + BorshDeserialize,
        H: ToKey,
    ensures
        view(final(m)) == view(old(m)).remove(*k),
        match r {
            Some(prev) => view(old(m)).dom().contains(*k) && prev == view(old(m))[*k],
            None       => !view(old(m)).dom().contains(*k),
        },
{
    m.remove(k)
}

/// Combined set/remove: `Some(v)` inserts, `None` removes.
#[verifier::external_body]
pub fn lm_set<K, V, H>(m: &mut LookupMap<K, V, H>, k: K, v: Option<V>)
    where
        K: BorshSerialize + Ord + Clone,
        V: BorshSerialize,
        H: ToKey,
    ensures
        view(final(m)) == match v {
            Some(val) => view(old(m)).insert(k, val),
            None      => view(old(m)).remove(k),
        },
{
    m.set(k, v)
}

// -- Cache management ---------------------------------------------------

/// Flush the in-memory cache to durable storage. No effect on the view.
#[verifier::external_body]
pub fn lm_flush<K, V, H>(m: &mut LookupMap<K, V, H>)
    where
        K: BorshSerialize + Ord,
        V: BorshSerialize,
        H: ToKey,
    ensures
        view(final(m)) == view(old(m)),
{
    m.flush()
}

} // verus!
