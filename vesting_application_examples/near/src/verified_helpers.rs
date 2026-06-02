// Verified kernel that `Vesting::claim` forwards to.
//
// Same pattern as the fungible NEAR contract's `verified_transfer`
// (and `verified_state.rs` in the linera_alternate fungible example):
// the contract's exposed method is a thin forwarder; all of the
// substantive logic — caller authorisation, time lookup, schedule
// arithmetic, monotonicity proof — lives here with `ensures` clauses
// that pin the abstract effect on `the_caller()` / `the_now()` and
// the spec-level `state_after_claim`.

use crate::near_axioms::{now_ms, panic_str, predecessor};
use near_sdk::AccountId;
use verus_vesting_core::{compute_claim, Params};

vstd::prelude::verus! {
    #[cfg(verus_only)]
    use vstd::prelude::*;
    #[cfg(verus_only)]
    use crate::core::{
        State, lemma_vested_bounded, state_after_claim,
    };
    #[cfg(verus_only)]
    use crate::near_axioms::{the_caller, the_now};

    /// Inputs/outputs that cross the verified boundary on a claim:
    ///
    ///   - `beneficiary` (in): the AccountId allowed to claim. The
    ///     verified body rejects any caller that isn't this one.
    ///     Passed by value (caller clones from `self.beneficiary`)
    ///     because `AccountId == AccountId` has a spec via
    ///     `assume_specification` while `&AccountId == &AccountId` does
    ///     not.
    ///   - `params` (in): the immutable schedule parameters set at init.
    ///   - `claimed` (in/out): how much the beneficiary has withdrawn
    ///     so far. Updated in place to reflect the new total.
    ///
    /// Returns: the amount released by *this* claim (the delta). The
    /// caller's job is to actually transfer that much native token to
    /// the beneficiary; this helper is responsible only for the
    /// accounting (which is the part with the interesting invariants).
    ///
    /// `ensures`:
    ///
    ///   - authorization: `the_caller() == beneficiary`.
    ///   - state-level connection: the post-state's `claimed` is
    ///     exactly `state_after_claim(pre_state, the_now()).claimed`.
    ///   - monotonicity: `claimed` only grows.
    ///   - the returned amount equals `post.claimed - pre.claimed`.
    pub fn verified_claim(
        beneficiary: AccountId,
        params:      &Params,
        claimed:     &mut u128,
    ) -> (released: u128)
        requires
            params.well_formed(),
            (*old(claimed) as nat) <= (params.total as nat),
        ensures
            // Caller authorization.
            the_caller() == beneficiary,
            // claimed only grows.
            *final(claimed) >= *old(claimed),
            // The returned amount is the exact delta in `claimed`.
            released as int == (*final(claimed) as int) - (*old(claimed) as int),
            // State-level connection: matches `state_after_claim` on
            // the abstract `State<AccountId>` view of (beneficiary,
            // params, claimed).
            (*final(claimed) as int)
                == (state_after_claim::<AccountId>(
                        State { beneficiary, params: *params, claimed: *old(claimed) },
                        the_now(),
                    ).claimed as int),
    {
        // 1. Authorization. The runtime says `predecessor()` is whoever
        //    called the entry point; we require that to be the
        //    beneficiary recorded at init.
        let caller = predecessor();
        if caller != beneficiary {
            panic_str("unauthorized: only the beneficiary may claim");
        }

        // 2. Time. `the_now()` is constant inside this method body, so
        //    Verus sees the value used in arithmetic match the value
        //    used in the ensures clause.
        let t = now_ms();

        // 3. Schedule lookup. `compute_claim`'s ensures connects the
        //    runtime u128 to the spec-level `claimable_at`.
        let amount = match compute_claim(params, t, *claimed) {
            Ok(a)  => a,
            Err(e) => { panic_str(e); 0 }, // panic_str diverges; the 0 is unreachable
        };

        // 4. Accounting update. The `if amount > 0` branch is
        //    pedagogical — Verus is happy either way — but it keeps
        //    the storage write off the no-op path, which matches what
        //    a careful contract would do (no spurious state-write gas).
        proof {
            // Bound the addition: amount == claimable_at(...) and
            // claimable_at(s, t) + s.claimed <= vested_at(t) <= total
            // (the two cases of claimable_at coincide once you fold
            //  this in). Calling the bounded lemma lets Verus discharge
            // the no-overflow check on `*claimed + amount`.
            lemma_vested_bounded(*params, t);
        }
        if amount > 0 {
            *claimed = *claimed + amount;
        }

        amount
    }
}
