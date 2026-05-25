// Axiomatization of NEAR's persistent key/value storage, hosted on our
// own wrapper type `AxLookupMap<K, V>`.
//
// We wrap `near_sdk::store::LookupMap<K, V, Identity>` rather than
// axiomatize it directly because near-sdk's `ToKey` trait has a
// `Sealed` super-trait in a private module, which Verus's
// `external_trait_specification` cannot reference. Wrapping in our own
// type sidesteps that — Verus is happy to reason about a struct we own.
//
// The wrapper is a one-line change at the call site: a contract that
// used `LookupMap<AccountId, u128>` now uses `AxLookupMap<AccountId,
// u128>`. The methods (`new`, `get`, `insert`, `contains_key`,
// `remove`, `set`, `flush`) keep their names and signatures, plus a
// `get_ref` companion for the by-reference read.
//
// The ghost projection is exposed via the `View` trait from vstd:
// `m@` is the abstract `Map<K, V>` content. This is the standard
// Verus pattern for talking about &self / &mut self in the same idiom.
//
// What is and isn't axiomatized:
//
//   axiomatized:
//     new           — empty view on construction
//     get           — read by value (Copy V), Option<V>
//     get_ref       — read by reference, Option<&V>
//     contains_key  — membership test
//     insert        — point update, returns prior Option<V>
//     remove        — point delete, returns prior Option<V>
//     set           — Some => insert, None => remove
//     flush         — write-back to storage; no semantic effect on view
//
//   NOT axiomatized (deliberately):
//     get_mut       — needs prophecy/borrow-tracking for &mut V return
//     entry         — entry API has a stateful return value
//     with_hasher   — wrapper is specialised to default `Identity` hasher
//
// TRUST: every line below this banner enlarges the TCB. The axioms claim
// what the wrapped `LookupMap`'s methods do; we trust the SDK to
// actually do it.

use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::map::*;
use near_sdk::store::LookupMap;
use near_sdk::store::key::Identity;
use near_sdk::borsh::{BorshDeserialize, BorshSerialize};
use near_sdk::IntoStorageKey;

verus! {

#[verifier::external_body]
#[verifier::accept_recursive_types(K)]
#[verifier::accept_recursive_types(V)]
pub struct AxLookupMap<K, V>
where
    K: BorshSerialize + BorshDeserialize + Ord,
    V: BorshSerialize + BorshDeserialize,
{
    inner: LookupMap<K, V, Identity>,
}

// Borsh impls are needed so `AxLookupMap` can sit in a NEAR contract
// state. Hand-written and marked external so Verus doesn't try to
// reason about field access on an opaque type.

#[verifier::external]
impl<K, V> BorshSerialize for AxLookupMap<K, V>
where
    K: BorshSerialize + BorshDeserialize + Ord,
    V: BorshSerialize + BorshDeserialize,
{
    fn serialize<W: near_sdk::borsh::io::Write>(&self, writer: &mut W) -> near_sdk::borsh::io::Result<()> {
        self.inner.serialize(writer)
    }
}

#[verifier::external]
impl<K, V> BorshDeserialize for AxLookupMap<K, V>
where
    K: BorshSerialize + BorshDeserialize + Ord,
    V: BorshSerialize + BorshDeserialize,
{
    fn deserialize_reader<R: near_sdk::borsh::io::Read>(reader: &mut R) -> near_sdk::borsh::io::Result<Self> {
        Ok(AxLookupMap { inner: LookupMap::deserialize_reader(reader)? })
    }
}


// -- External trait declarations ----------------------------------------

#[verifier::external_trait_specification]
pub trait ExBorshSerialize {
    type ExternalTraitSpecificationFor: BorshSerialize;
}

#[verifier::external_trait_specification]
pub trait ExBorshDeserialize: Sized {
    type ExternalTraitSpecificationFor: BorshDeserialize;
}

#[verifier::external_trait_specification]
pub trait ExIntoStorageKey {
    type ExternalTraitSpecificationFor: IntoStorageKey;
}

// -- Ghost projection via the View trait --------------------------------

impl<K, V> View for AxLookupMap<K, V>
where
    K: BorshSerialize + BorshDeserialize + Ord,
    V: BorshSerialize + BorshDeserialize,
{
    type V = Map<K, V>;

    uninterp spec fn view(&self) -> Map<K, V>;
}

impl<K, V> AxLookupMap<K, V>
where
    K: BorshSerialize + BorshDeserialize + Ord + Clone,
    V: BorshSerialize + BorshDeserialize,
{
    /// Construct an empty map with the given storage prefix.
    #[verifier::external_body]
    pub fn new<S>(prefix: S) -> (m: Self)
        where S: IntoStorageKey,
        ensures
            m@ == Map::<K, V>::empty(),
    {
        AxLookupMap { inner: LookupMap::new(prefix) }
    }

    /// Read by reference. `Some(v)` iff `k` is in the view's domain.
    #[verifier::external_body]
    pub fn get_ref<'a>(&'a self, k: &K) -> (r: Option<&'a V>)
        ensures
            match r {
                Some(v) => self@.dom().contains(*k) && *v == self@[*k],
                None    => !self@.dom().contains(*k),
            },
    {
        self.inner.get(k)
    }

    /// Membership test.
    #[verifier::external_body]
    pub fn contains_key(&self, k: &K) -> (r: bool)
        ensures r == self@.dom().contains(*k),
    {
        self.inner.contains_key(k)
    }

    /// Point insert. Returns the previous value if the key was present.
    #[verifier::external_body]
    pub fn insert(&mut self, k: K, v: V) -> (r: Option<V>)
        ensures
            final(self)@ == old(self)@.insert(k, v),
            match r {
                Some(prev) => old(self)@.dom().contains(k) && prev == old(self)@[k],
                None       => !old(self)@.dom().contains(k),
            },
    {
        self.inner.insert(k, v)
    }

    /// Point delete. Returns the previous value if the key was present.
    #[verifier::external_body]
    pub fn remove(&mut self, k: &K) -> (r: Option<V>)
        ensures
            final(self)@ == old(self)@.remove(*k),
            match r {
                Some(prev) => old(self)@.dom().contains(*k) && prev == old(self)@[*k],
                None       => !old(self)@.dom().contains(*k),
            },
    {
        self.inner.remove(k)
    }

    /// Combined set/remove: `Some(v)` inserts, `None` removes.
    #[verifier::external_body]
    pub fn set(&mut self, k: K, v: Option<V>)
        ensures
            final(self)@ == match v {
                Some(val) => old(self)@.insert(k, val),
                None      => old(self)@.remove(k),
            },
    {
        self.inner.set(k, v)
    }

    /// Flush the in-memory cache to durable storage. No effect on the view.
    #[verifier::external_body]
    pub fn flush(&mut self)
        ensures final(self)@ == old(self)@,
    {
        self.inner.flush()
    }
}

// Read by value (for `Copy` V like `u128`) — separate impl block because
// it adds a `V: Copy` bound the others don't need.
impl<K, V> AxLookupMap<K, V>
where
    K: BorshSerialize + BorshDeserialize + Ord + Clone,
    V: BorshSerialize + BorshDeserialize + Copy,
{
    /// Read by value. Friendlier than `get_ref` in arithmetic code.
    #[verifier::external_body]
    pub fn get(&self, k: &K) -> (r: Option<V>)
        ensures
            match r {
                Some(v) => self@.dom().contains(*k) && v == self@[*k],
                None    => !self@.dom().contains(*k),
            },
    {
        self.inner.get(k).copied()
    }
}

} // verus!
