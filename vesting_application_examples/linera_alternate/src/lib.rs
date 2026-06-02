// Linera (alternate sync SDK) linear-with-cliff vesting contract —
// verified core layer.
//
// Layout (mirrors `linera_alternate` fungible):
//   - `pub mod core;`              — re-export of the chain-agnostic
//                                    verified vesting core.
//   - `pub mod linera_axioms;`     — AccountOwner external type, caller
//                                    + time ghosts, PartialEq spec for
//                                    AccountOwner.
//   - `pub mod verified_helpers;`  — `verified_claim_step` (auth,
//                                    schedule, monotonicity).
//   - this file                    — module declarations + tests.
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
pub mod verified_helpers;

pub use verified_helpers::{verified_claim_step, ClaimError};

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
