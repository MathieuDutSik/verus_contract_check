// Verified kernel that the `#[ink(message)] fn claim` forwards to.
//
// Lives outside the `#[ink::contract]` module because the macro
// expansion is not Verus-friendly. The contract method reads
// `Self::env().caller()` and `Self::env().block_timestamp()`, fetches
// the stored `beneficiary` and `params` from `#[ink(storage)]`, then
// forwards to `verified_claim_step` here. The `AccountId` external
// spec + PartialEq axiom that this helper depends on live in
// `ink_axioms.rs`.
//
// Same pattern as `verified_state.rs` in the linera_alternate fungible
// example, and as the per-chain `verified_helpers.rs` files in the
// other vesting crates.

use ink::primitives::AccountId;
use verus_vesting_core::{compute_claim, Params};

vstd::prelude::verus! {
    #[cfg(verus_only)]
    use vstd::prelude::*;
    #[cfg(verus_only)]
    use crate::core::{
        State as CoreState, lemma_vested_bounded, state_after_claim,
    };

    /// Errors the verified claim helper raises. Mapped to the
    /// contract's `Error` enum in the `#[ink(message)] fn claim`
    /// glue.
    #[derive(PartialEq, Eq, Debug)]
    pub enum ClaimError {
        Unauthorized,
        ArithOverflow,
    }

    /// Verified claim step. The contract method reads `caller` and
    /// `now_ms` from the ink env, the stored `beneficiary` and
    /// `params` from `#[ink(storage)]`, and forwards them here. The
    /// helper authorises, schedules, and mutates `claimed`.
    ///
    /// `ensures` (success path):
    ///
    ///   - authorisation: `caller == beneficiary`.
    ///   - state-level connection: post `claimed` is exactly
    ///     `state_after_claim(...).claimed` on the abstract
    ///     `State<AccountId>` reconstructed from the parameters.
    ///   - monotonicity: `*final(claimed) >= *old(claimed)`.
    ///   - the returned amount equals the delta in `claimed`.
    pub fn verified_claim_step(
        caller:      AccountId,
        now_ms:      u64,
        beneficiary: AccountId,
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
                    &&& caller == beneficiary
                    &&& amount as int
                        == (*final(claimed) as int) - (*old(claimed) as int)
                    &&& *final(claimed) as int
                        == state_after_claim::<AccountId>(
                                CoreState {
                                    beneficiary,
                                    params:      *params,
                                    claimed:     *old(claimed),
                                },
                                now_ms,
                           ).claimed as int
                }
                Err(_) => true,
            },
    {
        if !(caller == beneficiary) {
            return Err(ClaimError::Unauthorized);
        }
        let amount = match compute_claim(params, now_ms, *claimed) {
            Ok(a)  => a,
            Err(_) => return Err(ClaimError::ArithOverflow),
        };
        proof {
            lemma_vested_bounded(*params, now_ms);
        }
        if amount > 0 {
            *claimed = *claimed + amount;
        }
        Ok(amount)
    }
}
