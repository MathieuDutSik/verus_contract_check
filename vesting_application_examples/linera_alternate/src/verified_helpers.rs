// Verified kernel that a Linera Contract `claim` operation forwards to.
//
// Direct analogue of `verified_state.rs` in the fungible_alternate
// example: the substantive logic — caller authorisation, schedule
// arithmetic, monotonicity proof — lives here with `ensures` clauses
// tied to the abstract spec-level `state_after_claim`. A Contract
// trait implementation would call this from `execute_operation`, after
// reading `runtime.authenticated_signer()` and `runtime.system_time()`.

use linera_sdk::linera_base_types::AccountOwner;
use verus_vesting_core::{compute_claim, Params};

vstd::prelude::verus! {
    #[cfg(verus_only)]
    use vstd::prelude::*;
    #[cfg(verus_only)]
    use crate::core::{
        State as CoreState, lemma_vested_bounded, state_after_claim,
    };

    /// Errors the verified claim helper raises.
    #[derive(PartialEq, Eq, Debug)]
    pub enum ClaimError {
        /// `authenticated_signer()` returned `None`, or returned a signer
        /// other than the registered beneficiary.
        Unauthorized,
        /// `compute_vested`'s arithmetic overflowed u128.
        ArithOverflow,
    }

    /// Verified claim kernel. Mirrors the shape used on every other
    /// chain: the contract's runtime handler reads the caller (here
    /// `Option<AccountOwner>` from `runtime.authenticated_signer()`)
    /// and the current time (microseconds from `runtime.system_time()`),
    /// then forwards them with the stored `beneficiary` + `params` +
    /// current `claimed`.
    ///
    /// `ensures` (success path):
    ///
    ///   - authorisation: `caller == Some(beneficiary)`.
    ///   - state-level connection: `*final(claimed) ==
    ///     state_after_claim(...).claimed` on the abstract
    ///     `State<AccountOwner>` reconstructed from the parameters.
    ///   - monotonicity: `*final(claimed) >= *old(claimed)`.
    ///   - the returned amount equals the delta in `claimed`.
    pub fn verified_claim_step(
        caller:        Option<AccountOwner>,
        now_micros:    u64,
        beneficiary:   AccountOwner,
        params:        &Params,
        claimed:       &mut u128,
    ) -> (r: Result<u128, ClaimError>)
        requires
            params.well_formed(),
            (*old(claimed) as nat) <= (params.total as nat),
        ensures
            *final(claimed) >= *old(claimed),
            match r {
                Ok(amount) => {
                    &&& caller == Some(beneficiary)
                    &&& amount as int
                        == (*final(claimed) as int) - (*old(claimed) as int)
                    &&& *final(claimed) as int
                        == state_after_claim::<AccountOwner>(
                                CoreState {
                                    beneficiary,
                                    params:      *params,
                                    claimed:     *old(claimed),
                                },
                                now_micros,
                           ).claimed as int
                }
                Err(_) => true,
            },
    {
        // 1. Authorisation. The runtime returns None when the operation
        //    isn't authenticated (e.g. it came from an unauthenticated
        //    cross-chain message); otherwise it returns the signer's
        //    AccountOwner. We allow only the beneficiary.
        let auth_signer = match caller {
            Some(a) => a,
            None    => return Err(ClaimError::Unauthorized),
        };
        if !(auth_signer == beneficiary) {
            return Err(ClaimError::Unauthorized);
        }

        // 2. Schedule lookup.
        let amount = match compute_claim(params, now_micros, *claimed) {
            Ok(a)  => a,
            Err(_) => return Err(ClaimError::ArithOverflow),
        };

        // 3. Bound the addition so `claimed + amount` doesn't overflow.
        proof {
            lemma_vested_bounded(*params, now_micros);
        }

        // 4. Accounting update.
        if amount > 0 {
            *claimed = *claimed + amount;
        }
        Ok(amount)
    }
}
