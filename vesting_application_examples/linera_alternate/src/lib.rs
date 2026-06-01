// Linera (alternate sync SDK) linear-with-cliff vesting contract —
// verified core layer.
//
// Layout:
//   - `pub mod core;`           — re-export of the chain-agnostic
//                                 verified vesting core.
//   - `pub mod linera_axioms;`  — AccountOwner external type, caller +
//                                 time ghosts, PartialEq spec for
//                                 AccountOwner.
//   - `verified_claim_step`     — the verified kernel (auth, schedule,
//                                 monotonicity).
//
// What we do NOT cover here:
//   - The full Contract / Service trait wiring (`linera_sdk::contract!`
//     and `linera_sdk::service!` macros). Those live in
//     `contract.rs` and `service.rs` for a deploy-ready artifact; we
//     omit them so the verification stays focused on the substantive
//     logic. The Contract glue would read `runtime.authenticated_signer()`
//     and `runtime.system_time()`, fetch the immutable schedule
//     params + the mutable `claimed` from a `SyncRootView`-backed
//     state, and forward to `verified_claim_step` — analogous to the
//     fungible alternate's state.rs forwarding to verified_credit /
//     verified_debit.
//   - Storage axiomatization for `RegisterView<T>` (vesting's natural
//     state holder). Same pragmatic shortcut as the MultiversX vesting
//     contract: the schedule/auth logic is verified; persistence is
//     unverified glue.
//
// Build modes:
//   cargo build                                       — rlib only.
//   cargo verus verify --target wasm32-unknown-unknown — verifies the
//                                                       core + verified
//                                                       _claim_step.

pub mod core;
pub mod linera_axioms;

use linera_sdk::linera_base_types::AccountOwner;
use verus_vesting_core::{compute_claim, Params};

vstd::prelude::verus! {
    #[cfg(verus_only)]
    use vstd::prelude::*;
    #[cfg(verus_only)]
    use crate::core::{
        State as CoreState, claimable_at, lemma_vested_bounded, state_after_claim,
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

#[cfg(test)]
mod tests {
    use verus_vesting_core::{compute_claim, compute_vested, Params};

    fn params() -> Params {
        Params {
            start:          1_000,
            cliff_duration: 500,
            vest_duration:  2_000,
            total:          1_000_000,
        }
    }

    #[test]
    fn pre_cliff_zero() {
        assert_eq!(compute_vested(&params(), 1_499).unwrap(), 0);
    }

    #[test]
    fn at_cliff_quarter() {
        assert_eq!(compute_vested(&params(), 1_500).unwrap(), 250_000);
    }

    #[test]
    fn mid_vest_half() {
        assert_eq!(compute_vested(&params(), 2_000).unwrap(), 500_000);
    }

    #[test]
    fn end_full() {
        assert_eq!(compute_vested(&params(), 3_000).unwrap(), 1_000_000);
    }

    #[test]
    fn claim_idempotent_same_time() {
        let p = params();
        let r = compute_claim(&p, 1_500, 0).unwrap();
        assert_eq!(r, 250_000);
        assert_eq!(compute_claim(&p, 1_500, 250_000).unwrap(), 0);
    }

    #[test]
    fn claim_two_blocks_sum_total() {
        let p = params();
        let r1 = compute_claim(&p, 2_000, 0).unwrap();
        let r2 = compute_claim(&p, 3_000, r1).unwrap();
        assert_eq!(r1 + r2, p.total);
    }
}
