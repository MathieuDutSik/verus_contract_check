// Verified kernels that the IC entry points forward to.
//
// Same pattern as the fungible IC contract's `verified_transfer` (and
// `verified_state.rs` in the linera_alternate example): the
// SDK-decorated `#[init]` / `#[update]` / `#[query]` glue is a thin
// forwarder; all of the substantive logic — caller authorisation,
// schedule arithmetic, monotonicity proof — lives here with `ensures`
// clauses that pin the abstract effect on `the_caller()` / `the_now_ns()`
// and the spec-level `state_after_claim`.

use candid::Principal;

use crate::ic_axioms::{caller, now_ns};
use verus_vesting_core::{compute_claim, compute_vested, Params};

vstd::prelude::verus! {
    #[cfg(verus_only)]
    use vstd::prelude::*;
    #[cfg(verus_only)]
    use crate::core::{
        State as CoreState, lemma_vested_bounded, state_after_claim,
    };
    #[cfg(verus_only)]
    use crate::ic_axioms::{the_caller, the_now_ns};

    /// Errors the verified claim helper raises. Mapped to a String by
    /// the entry-point glue.
    #[derive(PartialEq, Eq, Debug)]
    pub enum ClaimError {
        Unauthorized,
        ArithOverflow,
    }

    /// Verified `claim` step: release the currently-claimable amount
    /// to the registered beneficiary. The caller (via the ghost
    /// `the_caller()`) must equal `beneficiary`.
    ///
    /// `ensures` (success path):
    ///
    ///   - authorisation: `the_caller() == beneficiary`.
    ///   - state-level connection: `*final(claimed) == state_after_claim(
    ///     core_state(beneficiary, params, *old(claimed)), the_now_ns()
    ///   ).claimed`.
    ///   - monotonicity: `*final(claimed) >= *old(claimed)`.
    ///   - the returned amount equals the delta in `claimed`.
    ///   - `params` are unchanged (it's `&Params`, immutable).
    pub fn verified_claim(
        beneficiary: Principal,
        params:      &Params,
        claimed:     &mut u128,
    ) -> (r: Result<u128, ClaimError>)
        requires
            params.well_formed(),
            (*old(claimed) as nat) <= (params.total as nat),
        ensures
            // claimed monotone.
            *final(claimed) >= *old(claimed),
            match r {
                Ok(amount) => {
                    &&& the_caller() == beneficiary
                    &&& amount as int
                        == (*final(claimed) as int) - (*old(claimed) as int)
                    // State-level connection.
                    &&& *final(claimed) as int
                        == state_after_claim::<Principal>(
                                CoreState {
                                    beneficiary,
                                    params:      *params,
                                    claimed:     *old(claimed),
                                },
                                the_now_ns(),
                           ).claimed as int
                }
                Err(_) => true,
            },
    {
        // 1. Authorisation. Principal is Copy, so we compare owned
        //    values directly via the spec'd `<Principal as PartialEq>::eq`.
        let c = caller();
        if !(c == beneficiary) {
            return Err(ClaimError::Unauthorized);
        }

        // 2. Schedule lookup. `compute_claim`'s ensures connects the
        //    runtime u128 to the spec-level `claimable_at`.
        let t = now_ns();
        let amount = match compute_claim(params, t, *claimed) {
            Ok(a)  => a,
            Err(_) => return Err(ClaimError::ArithOverflow),
        };

        // 3. Bound the addition so `claimed + amount` can't overflow.
        proof {
            lemma_vested_bounded(*params, t);
        }

        // 4. Accounting update.
        if amount > 0 {
            *claimed = *claimed + amount;
        }
        Ok(amount)
    }

    /// Verified view: how much *would* be vested at `now_ns()`,
    /// ignoring the already-claimed amount.
    pub fn verified_vested_now(params: &Params) -> (r: Result<u128, ClaimError>)
        requires params.well_formed(),
    {
        let t = now_ns();
        match compute_vested(params, t) {
            Ok(v)  => Ok(v),
            Err(_) => Err(ClaimError::ArithOverflow),
        }
    }

    /// Verified view: how much could be claimed right now.
    pub fn verified_claimable_now(
        params:  &Params,
        claimed: u128,
    ) -> (r: Result<u128, ClaimError>)
        requires
            params.well_formed(),
            (claimed as nat) <= (params.total as nat),
    {
        let t = now_ns();
        match compute_claim(params, t, claimed) {
            Ok(a)  => Ok(a),
            Err(_) => Err(ClaimError::ArithOverflow),
        }
    }
}
