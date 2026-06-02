// Verified kernel that the MultiversX `claim` endpoint forwards to.
//
// Lives outside the `#[multiversx_sc::contract]` macro module because
// the macro expansion is not Verus-friendly. The endpoint reads the
// caller (`self.blockchain().get_caller()`) and the block timestamp
// (`self.blockchain().get_block_timestamp()`), fetches the stored
// `beneficiary` and `params` from the SingleValueMapper storage, then
// forwards them here.
//
// Same pattern as `verified_state.rs` in the linera_alternate fungible
// example, and as the per-chain `verified_helpers.rs` files in the
// other vesting crates.

use multiversx_sc::api::ManagedTypeApi;
use multiversx_sc::types::ManagedAddress;

use verus_vesting_core::{compute_claim, Params};

vstd::prelude::verus! {
    #[cfg(verus_only)]
    use vstd::prelude::*;
    #[cfg(verus_only)]
    use crate::vesting_core::{
        State as CoreState, lemma_vested_bounded, state_after_claim,
    };

    /// Errors the verified claim helper raises.
    #[derive(PartialEq, Eq, Debug)]
    pub enum ClaimError {
        Unauthorized,
        ArithOverflow,
    }

    /// Verified claim kernel. The contract endpoint reads the caller
    /// (via `self.blockchain().get_caller()`) and the block timestamp
    /// (via `self.blockchain().get_block_timestamp()`), then forwards
    /// them here with the stored `beneficiary` and `params`.
    ///
    /// `ensures` (success path):
    ///
    ///   - authorisation: `caller == beneficiary`.
    ///   - state-level connection: `*final(claimed) ==
    ///     state_after_claim(...).claimed`.
    ///   - monotonicity: `*final(claimed) >= *old(claimed)`.
    ///   - the returned amount equals the delta in `claimed`.
    pub fn verified_claim_step<M: ManagedTypeApi>(
        caller:      ManagedAddress<M>,
        now_secs:    u64,
        beneficiary: ManagedAddress<M>,
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
                        == state_after_claim::<ManagedAddress<M>>(
                                CoreState {
                                    beneficiary,
                                    params:      *params,
                                    claimed:     *old(claimed),
                                },
                                now_secs,
                           ).claimed as int
                }
                Err(_) => true,
            },
    {
        if !(caller == beneficiary) {
            return Err(ClaimError::Unauthorized);
        }
        let amount = match compute_claim(params, now_secs, *claimed) {
            Ok(a)  => a,
            Err(_) => return Err(ClaimError::ArithOverflow),
        };
        proof {
            lemma_vested_bounded(*params, now_secs);
        }
        if amount > 0 {
            *claimed = *claimed + amount;
        }
        Ok(amount)
    }
}
