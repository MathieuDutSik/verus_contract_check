// IC linear-with-cliff vesting contract with a Verus-verified core.
//
// Layout:
//   - `pub mod core;`        — chain-agnostic State<A> + schedule
//                              + monotonicity lemmas (identical to
//                              the NEAR / CosmWasm core).
//   - `pub mod ic_axioms;`   — IC-specific axioms: Principal external
//                              type, `caller()` / `now_ns()` / `trap()`
//                              wrappers tying into the ghost
//                              `the_caller()` / `the_now_ns()`.
//   - this file              — the actual contract: `VestingState`
//                              thread_local, the verified `claim`
//                              helper that takes the individual fields,
//                              and the SDK-decorated entry points.
//
// `VestingState` is kept outside `verus!{}` because it derives
// `CandidType` and `Deserialize`, which Verus treats as external. The
// verified helper instead takes `(beneficiary: Principal, params:
// &Params, claimed: &mut u128)` — same pattern as the NEAR vesting
// contract. Decomposing this way costs nothing at runtime (everything
// is in-memory, no extra reads) and keeps Verus's view of the
// substantive logic clean.
//
// Build modes:
//   cargo build              — wasm canister artifact.
//   cargo test               — runs the unit tests (schedule math; the
//                              IC runtime calls are not mockable in
//                              unit tests).
//   cargo verus verify --target wasm32-unknown-unknown
//                            — verifies the core + verified_claim.

pub mod core;
pub mod ic_axioms;

use candid::{CandidType, Principal};
use ic_cdk_macros::{init, query, update};
use serde::Deserialize;
use std::cell::RefCell;

use crate::ic_axioms::{caller, now_ns};
use verus_vesting_core::{compute_claim, compute_vested, Params};

/// Canister state. Set once at `init` and never re-initialised; only
/// `claimed` mutates afterwards.
#[derive(Default, CandidType, Deserialize, Clone)]
pub struct VestingState {
    pub beneficiary:       Option<Principal>,
    pub start_ns:          u64,
    pub cliff_duration_ns: u64,
    pub vest_duration_ns:  u64,
    pub total:             u128,
    pub claimed:           u128,
}

thread_local! {
    static STATE: RefCell<VestingState> = RefCell::new(VestingState::default());
}

vstd::prelude::verus! {
    #[cfg(verus_only)]
    use vstd::prelude::*;
    #[cfg(verus_only)]
    use crate::core::{
        State as CoreState, claimable_at, lemma_vested_bounded, state_after_claim,
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

// =====================================================================
// IC SDK glue (unverified): #[init], #[query], #[update] entry points,
// plus the candid `export_candid!` invocation. Each entry point reads
// the relevant pieces of state and forwards to a verified helper (or,
// for trivial reads, the candid query mechanism directly).
// =====================================================================

fn claim_err_to_string(e: ClaimError) -> String {
    match e {
        ClaimError::Unauthorized  => "unauthorized".into(),
        ClaimError::ArithOverflow => "schedule arithmetic overflow".into(),
    }
}

fn params_from(state: &VestingState) -> Params {
    Params {
        start:          state.start_ns,
        cliff_duration: state.cliff_duration_ns,
        vest_duration:  state.vest_duration_ns,
        total:          state.total,
    }
}

#[init]
fn init(
    beneficiary:       Principal,
    start_ns:          u64,
    cliff_duration_ns: u64,
    vest_duration_ns:  u64,
    total:             u128,
) {
    if vest_duration_ns == 0 {
        ic_cdk::trap("vest_duration_ns must be > 0");
    }
    if cliff_duration_ns > vest_duration_ns {
        ic_cdk::trap("cliff_duration_ns must be <= vest_duration_ns");
    }
    STATE.with(|s| {
        let mut state = s.borrow_mut();
        state.beneficiary       = Some(beneficiary);
        state.start_ns          = start_ns;
        state.cliff_duration_ns = cliff_duration_ns;
        state.vest_duration_ns  = vest_duration_ns;
        state.total             = total;
        state.claimed           = 0;
    });
}

#[query]
fn beneficiary() -> Option<Principal> {
    STATE.with(|s| s.borrow().beneficiary)
}

#[query]
fn total() -> u128 {
    STATE.with(|s| s.borrow().total)
}

#[query]
fn claimed() -> u128 {
    STATE.with(|s| s.borrow().claimed)
}

#[query]
fn vested_now() -> u128 {
    STATE.with(|s| {
        let state = s.borrow();
        let p = params_from(&state);
        match verified_vested_now(&p) {
            Ok(v)  => v,
            Err(e) => ic_cdk::trap(&claim_err_to_string(e)),
        }
    })
}

#[query]
fn claimable_now() -> u128 {
    STATE.with(|s| {
        let state = s.borrow();
        let p = params_from(&state);
        match verified_claimable_now(&p, state.claimed) {
            Ok(a)  => a,
            Err(e) => ic_cdk::trap(&claim_err_to_string(e)),
        }
    })
}

#[update]
fn claim() -> Result<u128, String> {
    STATE.with(|s| {
        let mut state = s.borrow_mut();
        let beneficiary = match state.beneficiary {
            Some(b) => b,
            None    => return Err("not initialized".into()),
        };
        let params = params_from(&state);
        verified_claim(beneficiary, &params, &mut state.claimed)
            .map_err(claim_err_to_string)
    })
}

ic_cdk::export_candid!();

#[cfg(test)]
mod tests {
    use verus_vesting_core::{compute_claim, compute_vested, Params};

    /// Standard test fixture: start=1000ns, cliff=500ns, vest=2000ns,
    /// total=1_000_000.
    fn params() -> Params {
        Params {
            start:          1_000,
            cliff_duration: 500,
            vest_duration:  2_000,
            total:          1_000_000,
        }
    }

    // ---- schedule math (compute_vested) ----

    #[test]
    fn pre_start_returns_zero() {
        let p = params();
        assert_eq!(compute_vested(&p, 500).unwrap(), 0);
    }

    #[test]
    fn pre_cliff_returns_zero() {
        let p = params();
        assert_eq!(compute_vested(&p, 1_499).unwrap(), 0);
    }

    #[test]
    fn at_cliff_proportional() {
        let p = params();
        assert_eq!(compute_vested(&p, 1_500).unwrap(), 250_000);
    }

    #[test]
    fn mid_vest_linear() {
        let p = params();
        assert_eq!(compute_vested(&p, 2_000).unwrap(), 500_000);
    }

    #[test]
    fn end_of_vest_full() {
        let p = params();
        assert_eq!(compute_vested(&p, 3_000).unwrap(), 1_000_000);
    }

    #[test]
    fn post_end_caps_at_total() {
        let p = params();
        assert_eq!(compute_vested(&p, 1_000_000_000).unwrap(), 1_000_000);
    }

    // ---- compute_claim with a pre-existing claimed snapshot ----

    #[test]
    fn claim_at_cliff_returns_quarter() {
        let p = params();
        assert_eq!(compute_claim(&p, 1_500, 0).unwrap(), 250_000);
    }

    #[test]
    fn claim_idempotent_at_same_time() {
        let p = params();
        assert_eq!(compute_claim(&p, 1_500, 250_000).unwrap(), 0);
    }

    #[test]
    fn claim_monotonic_across_two_times() {
        let p = params();
        let r1 = compute_claim(&p, 2_000, 0).unwrap();
        assert_eq!(r1, 500_000);
        let r2 = compute_claim(&p, 3_000, r1).unwrap();
        assert_eq!(r2, 500_000);
        assert_eq!(r1 + r2, p.total);
    }

    #[test]
    fn claim_post_end_drains_remaining() {
        let p = params();
        assert_eq!(compute_claim(&p, 10_000, 100_000).unwrap(), 900_000);
    }
}
