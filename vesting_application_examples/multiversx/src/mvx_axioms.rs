// Axiomatization of the MultiversX runtime calls the vesting contract
// uses.
//
// Carried over from the fungible MultiversX contract:
//   - `ManagedTypeApi` super-trait cascade (HandleTypeInfo /
//     StaticVarApi / ErrorApi) needed to declare `ManagedAddress<M>`.
//     The cascade is the "trait-cascade pattern" documented in
//     DESIGN.md.
//   - `ManagedAddress<M>` external_type_specification + PartialEq.
//
// New for vesting:
//   - `the_caller<M>()` ghost + `caller_of<M>(api)` wrapper around
//     `Blockchain::get_caller()`. The caller's ManagedAddress depends
//     on the contract's `M: ManagedTypeApi` parameter, hence the
//     generic ghost.
//   - `the_now_secs()` ghost + `now_secs_of<M>(api)` wrapper around
//     `Blockchain::get_block_timestamp()`. MVX uses *seconds* since
//     unix epoch (not ms or ns), so the schedule params downstream are
//     in seconds too.
//
// TRUST: every line below this banner enlarges the TCB.

use vstd::prelude::*;
use multiversx_sc::api::{ManagedTypeApi, HandleTypeInfo, StaticVarApi, ErrorApi};
use multiversx_sc::types::ManagedAddress;

verus! {

#[verifier::external_trait_specification]
pub trait ExHandleTypeInfo {
    type ExternalTraitSpecificationFor: HandleTypeInfo;
}

#[verifier::external_trait_specification]
pub trait ExStaticVarApi {
    type ExternalTraitSpecificationFor: StaticVarApi;
}

#[verifier::external_trait_specification]
pub trait ExErrorApi: HandleTypeInfo {
    type ExternalTraitSpecificationFor: ErrorApi;
}

#[verifier::external_trait_specification]
pub trait ExManagedTypeApi: HandleTypeInfo + StaticVarApi + ErrorApi + Clone + 'static {
    type ExternalTraitSpecificationFor: ManagedTypeApi;
}

// -- ManagedAddress ----------------------------------------------------

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::accept_recursive_types(M)]
pub struct ExManagedAddress<M: ManagedTypeApi>(#[allow(dead_code)] ManagedAddress<M>);

pub assume_specification<M: ManagedTypeApi>
    [ <ManagedAddress<M> as core::cmp::PartialEq>::eq ]
    (a: &ManagedAddress<M>, b: &ManagedAddress<M>) -> (r: bool)
    ensures r == (*a == *b);

// -- Caller + time ghosts ---------------------------------------------

/// The ghost caller of the current endpoint. Generic over `M` because
/// the runtime returns a `ManagedAddress<M>` tied to the contract's
/// API parameter.
pub uninterp spec fn the_caller<M: ManagedTypeApi>() -> ManagedAddress<M>;

/// The ghost block timestamp in *seconds* since the unix epoch.
/// MultiversX's `get_block_timestamp()` returns seconds, not ms; the
/// schedule parameters downstream are in seconds too.
pub uninterp spec fn the_now_secs() -> u64;

} // verus!
