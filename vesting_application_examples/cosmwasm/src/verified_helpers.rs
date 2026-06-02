// Verified kernels that the CosmWasm entry points forward to.
//
// Same pattern as the fungible CosmWasm contract's `verified_transfer`
// (and `verified_state.rs` in the linera_alternate example): the
// SDK-decorated `instantiate` / `execute` / `query` glue is a thin
// forwarder; all of the substantive logic — caller authorisation,
// schedule arithmetic, monotonicity proof, the abstract storage
// effect — lives here with `ensures` clauses that pin the effect on
// the ghost `*_view` projections from `cw_axioms.rs`.

use cosmwasm_std::{Addr, Storage};

use crate::cw_axioms::{
    ax_beneficiary_load, ax_beneficiary_save,
    ax_claimed_load, ax_claimed_save,
    ax_cliff_load, ax_cliff_save,
    ax_start_load, ax_start_save,
    ax_total_load, ax_total_save,
    ax_vest_load, ax_vest_save,
};
use verus_vesting_core::{compute_claim, Params};

vstd::prelude::verus! {
    #[cfg(verus_only)]
    use vstd::prelude::*;
    #[cfg(verus_only)]
    use crate::core::{
        State, lemma_vested_bounded, state_after_claim,
    };
    #[cfg(verus_only)]
    use crate::cw_axioms::{
        beneficiary_view, claimed_view, cliff_view, start_view,
        total_view, vest_view,
    };

    /// Errors the verified helpers raise. Chain-specific error mapping
    /// (to `ContractError` in `lib.rs`) happens in the entry-point glue.
    #[derive(PartialEq, Eq, Debug)]
    pub enum ClaimError {
        /// Caller isn't the registered beneficiary.
        Unauthorized,
        /// `compute_vested`'s arithmetic overflowed u128.
        ArithOverflow,
    }

    /// Spec-level summary: "all six storage views are populated AND
    /// the schedule is well-formed AND `claimed` is bounded by total".
    /// This is the invariant the contract maintains across instantiate
    /// and every subsequent claim. Used as a precondition on the
    /// verified helpers and as part of their postcondition.
    pub open spec fn vesting_ready<S: Storage>(s: &S) -> bool {
        &&& beneficiary_view(s).is_some()
        &&& start_view(s).is_some()
        &&& cliff_view(s).is_some()
        &&& vest_view(s).is_some()
        &&& total_view(s).is_some()
        &&& claimed_view(s).is_some()
        &&& (vest_view(s)->Some_0 > 0)
        &&& (cliff_view(s)->Some_0 <= vest_view(s)->Some_0)
        &&& (claimed_view(s)->Some_0 <= total_view(s)->Some_0)
    }

    /// Construct the `Params` view from the (assumed-populated) views.
    /// Used in the state-level ensures of `verified_claim`.
    pub open spec fn params_of<S: Storage>(s: &S) -> Params {
        Params {
            start:          start_view(s)->Some_0,
            cliff_duration: cliff_view(s)->Some_0,
            vest_duration:  vest_view(s)->Some_0,
            total:          total_view(s)->Some_0,
        }
    }

    /// Verified `instantiate`: persist the full bundle. The entry
    /// point checks `vest_duration > 0` and `cliff_duration <=
    /// vest_duration` (we *require* them) and validates the
    /// beneficiary string before calling in.
    ///
    /// Post: every view is `Some(<initial>)` and the invariant holds.
    pub fn verified_instantiate<S: Storage>(
        storage:        &mut S,
        beneficiary:    Addr,
        start_ms:       u64,
        cliff_duration: u64,
        vest_duration:  u64,
        total:          u128,
    )
        requires
            vest_duration > 0,
            cliff_duration <= vest_duration,
        ensures
            beneficiary_view(final(storage)) == Some(beneficiary),
            start_view(final(storage))       == Some(start_ms),
            cliff_view(final(storage))       == Some(cliff_duration),
            vest_view(final(storage))        == Some(vest_duration),
            total_view(final(storage))       == Some(total),
            claimed_view(final(storage))     == Some(0u128),
            vesting_ready(final(storage)),
    {
        ax_beneficiary_save(storage, &beneficiary);
        ax_start_save(storage, start_ms);
        ax_cliff_save(storage, cliff_duration);
        ax_vest_save(storage, vest_duration);
        ax_total_save(storage, total);
        ax_claimed_save(storage, 0);
    }

    /// Verified `claim`: release everything currently claimable to the
    /// beneficiary, gated on the caller matching the registered one.
    ///
    /// Returns the amount released this call.
    ///
    /// `ensures` (success path):
    ///
    ///   - authorisation: caller == registered beneficiary.
    ///   - state-level connection: post `claimed` is exactly
    ///     `state_after_claim(pre_state, now_ms).claimed`, where
    ///     `pre_state` is the spec-level `State<Addr>` reconstructed
    ///     from the storage views.
    ///   - monotonicity: post.claimed >= pre.claimed.
    ///   - returned amount equals the delta in claimed.
    ///   - the five immutable views (beneficiary, start, cliff, vest,
    ///     total) are preserved verbatim.
    ///   - the invariant `vesting_ready` is preserved.
    pub fn verified_claim<S: Storage>(
        storage:  &mut S,
        sender:   &Addr,
        now_ms:   u64,
    ) -> (r: Result<u128, ClaimError>)
        requires vesting_ready(old(storage)),
        ensures
            // Invariant always preserved.
            vesting_ready(final(storage)),
            // Five immutable views never change.
            beneficiary_view(final(storage)) == beneficiary_view(old(storage)),
            start_view(final(storage))       == start_view(old(storage)),
            cliff_view(final(storage))       == cliff_view(old(storage)),
            vest_view(final(storage))        == vest_view(old(storage)),
            total_view(final(storage))       == total_view(old(storage)),
            // claimed is monotone.
            claimed_view(final(storage))->Some_0 >= claimed_view(old(storage))->Some_0,
            // Result-specific.
            match r {
                Ok(amount) => {
                    let pre  = claimed_view(old(storage))->Some_0;
                    let post = claimed_view(final(storage))->Some_0;
                    &&& *sender == beneficiary_view(old(storage))->Some_0
                    &&& amount as int == (post as int) - (pre as int)
                    // State-level connection: post == state_after_claim
                    &&& post as int
                        == state_after_claim::<Addr>(
                                State {
                                    beneficiary: beneficiary_view(old(storage))->Some_0,
                                    params:      params_of(old(storage)),
                                    claimed:     pre,
                                },
                                now_ms,
                           ).claimed as int
                }
                Err(_) => true,
            },
    {
        // 1. Authorization. UFCS form `<Addr as PartialEq>::eq(...)`
        //    routes to the spec'd `assume_specification` in cw_axioms;
        //    the surface form `sender == &beneficiary` would resolve
        //    to the blanket `<&Addr as PartialEq<&Addr>>::eq` and
        //    Verus has no spec for that.
        let beneficiary = ax_beneficiary_load(storage);
        if !<Addr as ::core::cmp::PartialEq>::eq(sender, &beneficiary) {
            return Err(ClaimError::Unauthorized);
        }

        // 2. Read the immutable schedule + the mutable claimed.
        let start          = ax_start_load(storage);
        let cliff_duration = ax_cliff_load(storage);
        let vest_duration  = ax_vest_load(storage);
        let total          = ax_total_load(storage);
        let claimed_pre    = ax_claimed_load(storage);

        let params = Params { start, cliff_duration, vest_duration, total };

        // 3. Schedule lookup.
        let amount = match compute_claim(&params, now_ms, claimed_pre) {
            Ok(a)  => a,
            Err(_) => return Err(ClaimError::ArithOverflow),
        };

        // 4. Bound the addition for the no-overflow check. The bounded
        //    lemma gives `vested_at(p, now_ms) <= total`; chained with
        //    `compute_claim`'s post this caps `claimed_pre + amount`
        //    at `total`.
        proof {
            lemma_vested_bounded(params, now_ms);
        }

        // 5. Write back the new claimed (only if it changed, to skip
        //    the no-op storage write).
        if amount > 0 {
            ax_claimed_save(storage, claimed_pre + amount);
        }
        Ok(amount)
    }

    /// Verified view: how much *would* be vested at `now_ms`, ignoring
    /// the already-claimed amount.
    pub fn verified_vested<S: Storage>(
        storage: &S,
        now_ms:  u64,
    ) -> (r: Result<u128, ClaimError>)
        requires vesting_ready(storage),
    {
        let start          = ax_start_load(storage);
        let cliff_duration = ax_cliff_load(storage);
        let vest_duration  = ax_vest_load(storage);
        let total          = ax_total_load(storage);
        let params = Params { start, cliff_duration, vest_duration, total };
        match verus_vesting_core::compute_vested(&params, now_ms) {
            Ok(v)  => Ok(v),
            Err(_) => Err(ClaimError::ArithOverflow),
        }
    }
}
