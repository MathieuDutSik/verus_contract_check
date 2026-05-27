// BigUint axiomatization attempt — currently blocked.
//
// The goal: axiomatize `BigUint<M>` so the contract's `transfer` endpoint
// can route through a verified arithmetic kernel. BigUint is *conceptually*
// simpler than u128 here because it is unbounded by construction, so the
// kernel's spec maps 1-to-1 onto `nat` with no overflow caveats:
//
//   pub fn verified_transfer_big<M: ManagedTypeApi>(
//       from_balance: BigUint<M>, to_balance: BigUint<M>, amount: &BigUint<M>,
//   ) -> Result<(BigUint<M>, BigUint<M>), ()>
//       ensures Ok((f, t)) =>
//           biguint_val(&f) + biguint_val(&t)
//               == biguint_val(&from_balance) + biguint_val(&to_balance);
//
// Where this hits the wall: `BigUint<M: ManagedTypeApi>` requires Verus to
// know the `ManagedTypeApi` trait. Declaring it via `external_trait_specification`
// requires the proxy's `ExternalTraitSpecificationFor` associated type to
// match the trait's super-trait set exactly. `ManagedTypeApi` has five
// super-traits:
//
//     ManagedTypeApi: HandleTypeInfo + StaticVarApi + ErrorApi + Clone + 'static
//
// Verus's current syntax allows only **one bound** on `ExternalTraitSpecificationFor`:
//
//     // tried — errors "only one bound allowed"
//     type ExternalTraitSpecificationFor: ManagedTypeApi + HandleTypeInfo + ...;
//
//     // tried — bounds aren't recognized in where clauses either
//     type ExternalTraitSpecificationFor: ManagedTypeApi
//     where Self::ExternalTraitSpecificationFor: HandleTypeInfo, ...;
//
//     // tried — trait-level where clauses get counted as extra associated-type bounds
//     pub trait ExManagedTypeApi
//     where <Self as ExManagedTypeApi>::ExternalTraitSpecificationFor: HandleTypeInfo, ...
//     { type ExternalTraitSpecificationFor: ManagedTypeApi; }
//
// All three fail. This is the same class of obstacle as NEAR's `Sealed`
// super-trait (DESIGN.md). The escape hatches documented there are:
//   (a) A Verus extension that lifts the one-bound restriction.
//   (b) A newtype `AxBigUint` specialized to a concrete `M` (the way
//       NEAR's `AxLookupMap<K, V, Identity>` is specialized to the
//       default hasher). Unlike near-sdk's `Identity`, multiversx-sc
//       does not expose a single concrete `M: ManagedTypeApi` that's
//       always usable — the macro expansion injects `Self::Api`, which
//       is itself an associated type. So (b) is not directly available
//       without further plumbing.
//
// The fully-written-out axiomatization (in case Verus gains the missing
// feature) would look like:
//
//   #[verifier::external_type_specification]
//   #[verifier::external_body]
//   #[verifier::accept_recursive_types(M)]
//   pub struct ExBigUint<M: ManagedTypeApi>(BigUint<M>);
//
//   pub uninterp spec fn biguint_val<M: ManagedTypeApi>(x: &BigUint<M>) -> nat;
//
//   #[verifier::external_body]
//   pub fn biguint_ge<M: ManagedTypeApi>(a: &BigUint<M>, b: &BigUint<M>) -> (r: bool)
//       ensures r == (biguint_val(a) >= biguint_val(b));
//
//   #[verifier::external_body]
//   pub fn biguint_sub<M: ManagedTypeApi>(a: BigUint<M>, b: &BigUint<M>) -> (r: BigUint<M>)
//       requires biguint_val(&a) >= biguint_val(b),
//       ensures biguint_val(&r) == (biguint_val(&a) - biguint_val(b)) as nat;
//
//   #[verifier::external_body]
//   pub fn biguint_add_assign<M: ManagedTypeApi>(target: &mut BigUint<M>, other: &BigUint<M>)
//       ensures biguint_val(final(target)) == biguint_val(old(target)) + biguint_val(other);
//
// This file is left as documentation; nothing in it is compiled.
