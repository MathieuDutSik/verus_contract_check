// Experiment: express ManagedTypeApi's super-trait closure via proxy-trait
// inheritance rather than by stacking bounds on `ExternalTraitSpecificationFor`.
//
// If this works, the pattern generalizes: for any external trait with N
// super-traits, declare an external_trait_specification for each super-trait,
// and let the top-level proxy `inherit` from the super-trait proxies via Rust's
// `pub trait ExTop: ExSuper1 + ExSuper2 + ... { ... }` syntax.

use vstd::prelude::*;
use multiversx_sc::api::{ManagedTypeApi, HandleTypeInfo, StaticVarApi, ErrorApi};
use multiversx_sc::types::{BigUint, ManagedAddress};

verus! {

#[verifier::external_trait_specification]
pub trait ExHandleTypeInfo {
    type ExternalTraitSpecificationFor: HandleTypeInfo;
}

#[verifier::external_trait_specification]
pub trait ExStaticVarApi {
    type ExternalTraitSpecificationFor: StaticVarApi;
}

// ErrorApi: HandleTypeInfo — bound on the proxy via the external trait itself
#[verifier::external_trait_specification]
pub trait ExErrorApi: HandleTypeInfo {
    type ExternalTraitSpecificationFor: ErrorApi;
}

// ManagedTypeApi: HandleTypeInfo + StaticVarApi + ErrorApi + Clone + 'static
#[verifier::external_trait_specification]
pub trait ExManagedTypeApi: HandleTypeInfo + StaticVarApi + ErrorApi + Clone + 'static {
    type ExternalTraitSpecificationFor: ManagedTypeApi;
}

// -- BigUint -----------------------------------------------------------

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::accept_recursive_types(M)]
pub struct ExBigUint<M: ManagedTypeApi>(#[allow(dead_code)] BigUint<M>);

/// Ghost projection: the unbounded natural-number value of a `BigUint`.
pub uninterp spec fn biguint_val<M: ManagedTypeApi>(x: &BigUint<M>) -> nat;

#[verifier::external_body]
pub fn biguint_ge<M: ManagedTypeApi>(a: &BigUint<M>, b: &BigUint<M>) -> (r: bool)
    ensures r == (biguint_val(a) >= biguint_val(b)),
{
    a >= b
}

#[verifier::external_body]
pub fn biguint_sub<M: ManagedTypeApi>(a: BigUint<M>, b: &BigUint<M>) -> (r: BigUint<M>)
    requires biguint_val(&a) >= biguint_val(b),
    ensures biguint_val(&r) == (biguint_val(&a) - biguint_val(b)) as nat,
{
    a - b
}

#[verifier::external_body]
pub fn biguint_add_assign<M: ManagedTypeApi>(target: &mut BigUint<M>, other: &BigUint<M>)
    ensures biguint_val(final(target)) == biguint_val(old(target)) + biguint_val(other),
{
    *target += other;
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

} // verus!
