// IC linear-with-cliff vesting contract with a Verus-verified core.
//
// Layout (mirrors `linera_alternate` fungible):
//   - `pub mod core;`              — chain-agnostic verified core.
//   - `pub mod ic_axioms;`         — IC runtime axioms (Principal,
//                                    `caller()` / `now_ns()` / `trap()`
//                                    + ghosts).
//   - `pub mod verified_helpers;`  — `verified_claim`,
//                                    `verified_vested_now`,
//                                    `verified_claimable_now`.
//   - this file                    — `VestingState` thread_local,
//                                    `#[init]` / `#[query]` / `#[update]`
//                                    entry-point forwarders, tests.
//
// `VestingState` is kept outside `verus!{}` because it derives
// `CandidType` and `Deserialize`, which Verus treats as external. The
// verified helpers in `verified_helpers.rs` instead take
// `(Principal, &Params, &mut u128)` — same field-passing pattern as
// the NEAR vesting contract.
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
pub mod verified_helpers;

use candid::{CandidType, Principal};
use ic_cdk_macros::{init, query, update};
use serde::Deserialize;
use std::cell::RefCell;

use crate::verified_helpers::{
    verified_claim, verified_claimable_now, verified_vested_now, ClaimError,
};
use verus_vesting_core::Params;

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
