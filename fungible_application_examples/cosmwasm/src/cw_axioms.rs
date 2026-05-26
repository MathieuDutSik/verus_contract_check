// Axiomatization of cosmwasm's persistent storage for the balances map.
//
// CosmWasm's data model is different from NEAR's: instead of one
// self-contained collection type (`LookupMap`), storage is split into
//   - `Storage` (a trait object provided by the runtime, addressed as
//     `&dyn Storage` / `&mut dyn Storage`), and
//   - `Map<K, V>` (a typed handle from `cw_storage_plus`, a zero-sized
//     `const` that knows only the storage prefix and the K/V types).
//
// Rather than axiomatize the (Storage, Map) split, we expose a small
// pair of operations — `ax_balances_load`, `ax_balances_save` — that
// describe the effect of a balance read/write on the abstract view of
// the storage's balances.
//
// What is and isn't axiomatized:
//   axiomatized:
//     ax_balances_load — point read of one account, default 0
//     ax_balances_save — point write
//     ax_balances_has  — membership test
//     ax_supply_load   — read of TOTAL_SUPPLY
//     ax_supply_save   — write to TOTAL_SUPPLY
//
//   NOT axiomatized (deliberately):
//     Map's range iterators — defer; not used by the basic transfer
//     StdError details      — we assume operations never fail at the
//                             storage layer (no I/O errors)
//
// TRUST: every line below this banner enlarges the TCB. The axioms claim
// what these operations do; we trust cosmwasm-std + cw-storage-plus to
// actually do them.

use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::map::Map as SpecMap;
use cosmwasm_std::{Addr, Storage, Uint128, StdError};
use cw_storage_plus::{Item, Map};

// Storage handles. Constants so we share one address-space view of
// storage across the whole contract.
pub const BALANCES:     Map<&Addr, Uint128>             = Map::new("balances");
pub const TOTAL_SUPPLY: Item<Uint128>                   = Item::new("total_supply");
pub const ALLOWANCES:   Map<(&Addr, &Addr), Uint128>    = Map::new("allowances");
pub const MINTER:       Item<Addr>                      = Item::new("minter");

verus! {

// -- External type/trait declarations -----------------------------------

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExAddr(#[allow(dead_code)] Addr);

// Equality on Addr. PartialEq::eq returns true iff the two values are
// equal at the Verus level. Required because `if a == b` in exec code
// lowers to a `PartialEq::eq` call.
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

// -- Ghost projections --------------------------------------------------

/// The abstract `Map<Addr, u128>` content of the storage's `BALANCES`
/// map. Uninterpreted — the axiomatized operations below are the only
/// thing said about it.
pub uninterp spec fn balances_view<S: Storage>(storage: &S) -> SpecMap<Addr, u128>;

/// The abstract scalar value of the storage's `TOTAL_SUPPLY` item.
pub uninterp spec fn supply_view<S: Storage>(storage: &S) -> u128;

/// The abstract `Map<(Owner, Spender), u128>` content of the storage's
/// `ALLOWANCES` map.
pub uninterp spec fn allowances_view<S: Storage>(storage: &S) -> SpecMap<(Addr, Addr), u128>;

/// The current minter, if set. `None` means no minter (mint disabled).
pub uninterp spec fn minter_view<S: Storage>(storage: &S) -> Option<Addr>;

// -- Balance reads ------------------------------------------------------

/// Read the balance of `k`, treating absent entries as 0.
#[verifier::external_body]
pub fn ax_balances_load<S: Storage>(storage: &S, k: &Addr) -> (r: u128)
    ensures
        r == if balances_view(storage).dom().contains(*k) {
            balances_view(storage)[*k]
        } else {
            0u128
        },
{
    BALANCES.may_load(storage, k).unwrap().map(|v| v.u128()).unwrap_or(0)
}

/// Membership test.
#[verifier::external_body]
pub fn ax_balances_has<S: Storage>(storage: &S, k: &Addr) -> (r: bool)
    ensures r == balances_view(storage).dom().contains(*k),
{
    BALANCES.has(storage, k)
}

// -- Balance writes -----------------------------------------------------

/// Point insert / overwrite. Touches the balances map only; supply,
/// allowances, and minter are unchanged.
#[verifier::external_body]
pub fn ax_balances_save<S: Storage>(storage: &mut S, k: &Addr, v: u128)
    ensures
        balances_view(final(storage))   == balances_view(old(storage)).insert(*k, v),
        supply_view(final(storage))     == supply_view(old(storage)),
        allowances_view(final(storage)) == allowances_view(old(storage)),
        minter_view(final(storage))     == minter_view(old(storage)),
{
    BALANCES.save(storage, k, &Uint128::new(v)).unwrap()
}

// -- Total supply -------------------------------------------------------

#[verifier::external_body]
pub fn ax_supply_load<S: Storage>(storage: &S) -> (r: u128)
    ensures r == supply_view(storage),
{
    TOTAL_SUPPLY.load(storage).unwrap().u128()
}

#[verifier::external_body]
pub fn ax_supply_save<S: Storage>(storage: &mut S, v: u128)
    ensures
        supply_view(final(storage))     == v,
        balances_view(final(storage))   == balances_view(old(storage)),
        allowances_view(final(storage)) == allowances_view(old(storage)),
        minter_view(final(storage))     == minter_view(old(storage)),
{
    TOTAL_SUPPLY.save(storage, &Uint128::new(v)).unwrap()
}

// -- Allowances --------------------------------------------------------

/// Read the allowance `(owner, spender) → amount`, defaulting absent to 0.
#[verifier::external_body]
pub fn ax_allowances_load<S: Storage>(storage: &S, owner: &Addr, spender: &Addr) -> (r: u128)
    ensures
        r == if allowances_view(storage).dom().contains((*owner, *spender)) {
            allowances_view(storage)[(*owner, *spender)]
        } else {
            0u128
        },
{
    ALLOWANCES.may_load(storage, (owner, spender)).unwrap().map(|v| v.u128()).unwrap_or(0)
}

/// Set the allowance `(owner, spender) → amount`. Touches allowances
/// only; balances, supply, and minter are unchanged.
#[verifier::external_body]
pub fn ax_allowances_save<S: Storage>(storage: &mut S, owner: &Addr, spender: &Addr, amount: u128)
    ensures
        allowances_view(final(storage))
            == allowances_view(old(storage)).insert((*owner, *spender), amount),
        balances_view(final(storage)) == balances_view(old(storage)),
        supply_view(final(storage))   == supply_view(old(storage)),
        minter_view(final(storage))   == minter_view(old(storage)),
{
    ALLOWANCES.save(storage, (owner, spender), &Uint128::new(amount)).unwrap()
}

// -- Minter -------------------------------------------------------------

/// Read the current minter, if set.
#[verifier::external_body]
pub fn ax_minter_load<S: Storage>(storage: &S) -> (r: Option<Addr>)
    ensures r == minter_view(storage),
{
    MINTER.may_load(storage).unwrap()
}

/// Set the minter. Touches minter only; balances, supply, allowances unchanged.
#[verifier::external_body]
pub fn ax_minter_save<S: Storage>(storage: &mut S, addr: &Addr)
    ensures
        minter_view(final(storage))     == Some(*addr),
        balances_view(final(storage))   == balances_view(old(storage)),
        supply_view(final(storage))     == supply_view(old(storage)),
        allowances_view(final(storage)) == allowances_view(old(storage)),
{
    MINTER.save(storage, addr).unwrap()
}

} // verus!
