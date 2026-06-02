// Verified kernels that the Gear `handle()` entry point forwards to.
//
// `apply_claim` takes `sender` and `now` as explicit parameters so it
// can be shared between the production path (which reads them from the
// Gear runtime via the axiomatised `source()` / `now_ms()`) and the
// unit-test path (which injects them). `verified_claim` is the thin
// runtime-facing wrapper that does the read-from-runtime + delegate.
//
// Same shape as the fungible Gear contract's `apply_transfer` /
// `verified_transfer` pair, and analogous to `verified_state.rs` in
// the linera_alternate fungible example.

use gstd::ActorId;

use crate::gear_axioms::{now_ms, source};
use verus_vesting_core::{compute_claim, Params};

vstd::prelude::verus! {
    #[cfg(verus_only)]
    use vstd::prelude::*;
    #[cfg(verus_only)]
    use crate::core::{
        State as CoreState, lemma_vested_bounded, state_after_claim,
    };
    #[cfg(verus_only)]
    use crate::gear_axioms::{the_sender, the_now_ms};

    /// Errors the verified helpers raise.
    #[derive(PartialEq, Eq, Debug)]
    pub enum ClaimError {
        Unauthorized,
        ArithOverflow,
    }

    /// Verified claim kernel: the substantive logic, taking `sender`
    /// and `now` as explicit parameters so it's shared between the
    /// production path (which reads them from `msg::source()` /
    /// `exec::block_timestamp()`) and the unit-test path.
    ///
    /// `ensures` (success path):
    ///
    ///   - authorisation: `sender == beneficiary`.
    ///   - state-level connection: `*final(claimed) == state_after_claim(
    ///     CoreState { beneficiary, params: *params, claimed: *old(claimed) },
    ///     now ).claimed`.
    ///   - monotonicity: `*final(claimed) >= *old(claimed)`.
    ///   - the returned amount equals the delta in `claimed`.
    pub fn apply_claim(
        sender:      ActorId,
        now:         u64,
        beneficiary: ActorId,
        params:      &Params,
        claimed:     &mut u128,
    ) -> (r: Result<u128, ClaimError>)
        requires
            params.well_formed(),
            (*old(claimed) as nat) <= (params.total as nat),
        ensures
            *final(claimed) >= *old(claimed),
            match r {
                Ok(amount) => {
                    &&& sender == beneficiary
                    &&& amount as int
                        == (*final(claimed) as int) - (*old(claimed) as int)
                    &&& *final(claimed) as int
                        == state_after_claim::<ActorId>(
                                CoreState {
                                    beneficiary,
                                    params:      *params,
                                    claimed:     *old(claimed),
                                },
                                now,
                           ).claimed as int
                }
                Err(_) => true,
            },
    {
        if !(sender == beneficiary) {
            return Err(ClaimError::Unauthorized);
        }
        let amount = match compute_claim(params, now, *claimed) {
            Ok(a)  => a,
            Err(_) => return Err(ClaimError::ArithOverflow),
        };
        proof {
            lemma_vested_bounded(*params, now);
        }
        if amount > 0 {
            *claimed = *claimed + amount;
        }
        Ok(amount)
    }

    /// Verified claim entry point. Reads the sender via the axiomatised
    /// `source()` and the time via `now_ms()`, then delegates to
    /// `apply_claim`. This is what production `handle()` calls.
    pub fn verified_claim(
        beneficiary: ActorId,
        params:      &Params,
        claimed:     &mut u128,
    ) -> (r: Result<u128, ClaimError>)
        requires
            params.well_formed(),
            (*old(claimed) as nat) <= (params.total as nat),
        ensures
            *final(claimed) >= *old(claimed),
            match r {
                Ok(amount) => {
                    &&& the_sender() == beneficiary
                    &&& amount as int
                        == (*final(claimed) as int) - (*old(claimed) as int)
                    &&& *final(claimed) as int
                        == state_after_claim::<ActorId>(
                                CoreState {
                                    beneficiary,
                                    params:      *params,
                                    claimed:     *old(claimed),
                                },
                                the_now_ms(),
                           ).claimed as int
                }
                Err(_) => true,
            },
    {
        let sender = source();
        let now    = now_ms();
        apply_claim(sender, now, beneficiary, params, claimed)
    }
}
