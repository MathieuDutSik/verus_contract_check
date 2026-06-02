// NEAR linear-with-cliff vesting contract with a Verus-verified core.
//
// The contract is ordinary NEAR — `#[near(contract_state)]` struct,
// `#[init]` constructor, two view methods and one mutating method.
// The substantive logic of `claim` (caller-check, schedule lookup,
// arithmetic, monotonicity proof) lives in `verified_helpers.rs` as
// `verified_claim`; the contract method below is a one-line forwarder.
//
// Layout (mirrors `linera_alternate` fungible):
//   - `pub mod core;`              — chain-agnostic verified core.
//   - `pub mod near_axioms;`       — NEAR runtime axioms
//                                    (`predecessor()` / `now_ms()` /
//                                    `panic_str()` + ghosts).
//   - `pub mod verified_helpers;`  — `verified_claim` kernel.
//   - this file                    — `Vesting` struct + `#[near] impl`
//                                    forwarders + tests.
//
// Build modes:
//   cargo build                                       — wasm deploy artifact.
//   cargo test --target $HOST_TRIPLE                  — runs the unit tests.
//   cargo verus verify --target wasm32-unknown-unknown — verifies `core`
//                                                      + `verified_claim`.

pub mod core;
pub mod near_axioms;
pub mod verified_helpers;

use crate::verified_helpers::verified_claim;
use near_sdk::{near, AccountId, PanicOnDefault};
use verus_vesting_core::Params;

#[near(contract_state)]
#[derive(PanicOnDefault)]
pub struct Vesting {
    beneficiary: AccountId,
    /// Start of the vest, in ms since unix epoch.
    start: u64,
    /// Cliff length in ms. Before `start + cliff_duration` nothing
    /// vests.
    cliff_duration: u64,
    /// Total vesting length in ms. At `start + vest_duration` the
    /// whole `total` is released.
    vest_duration: u64,
    /// Grant size in native token units (smallest denomination).
    total: u128,
    /// How much has been claimed so far.
    claimed: u128,
}

#[near]
impl Vesting {
    /// Initialise the grant. `vest_duration` must be positive and at
    /// least as long as `cliff_duration`; the constructor panics
    /// otherwise (these are the same conditions
    /// `verus_vesting_core::Params::well_formed` checks).
    #[init]
    pub fn new(
        beneficiary: AccountId,
        start_ms: u64,
        cliff_duration_ms: u64,
        vest_duration_ms: u64,
        total: u128,
    ) -> Self {
        if vest_duration_ms == 0 {
            near_sdk::env::panic_str("vest_duration must be > 0");
        }
        if cliff_duration_ms > vest_duration_ms {
            near_sdk::env::panic_str("cliff_duration must be <= vest_duration");
        }
        Self {
            beneficiary,
            start: start_ms,
            cliff_duration: cliff_duration_ms,
            vest_duration: vest_duration_ms,
            total,
            claimed: 0,
        }
    }

    /// Read-only: how much has been released to date.
    pub fn claimed_amount(&self) -> u128 { self.claimed }

    /// Read-only: total grant size.
    pub fn total(&self) -> u128 { self.total }

    /// Read-only: the beneficiary.
    pub fn beneficiary(&self) -> AccountId { self.beneficiary.clone() }

    /// Read-only: how much *would* be vested at the current block's
    /// timestamp, ignoring what has already been claimed.
    pub fn vested_now(&self) -> u128 {
        let p = self.params();
        let t = near_sdk::env::block_timestamp_ms();
        match verus_vesting_core::compute_vested(&p, t) {
            Ok(v)  => v,
            Err(e) => near_sdk::env::panic_str(e),
        }
    }

    /// Read-only: how much could be claimed right now.
    pub fn claimable_now(&self) -> u128 {
        let p = self.params();
        let t = near_sdk::env::block_timestamp_ms();
        match verus_vesting_core::compute_claim(&p, t, self.claimed) {
            Ok(a)  => a,
            Err(e) => near_sdk::env::panic_str(e),
        }
    }

    /// Mutating: release everything currently claimable to the
    /// beneficiary. Reverts if the caller isn't the beneficiary.
    /// Returns the amount released this call (may be 0 if already
    /// caught up to the schedule).
    pub fn claim(&mut self) -> u128 {
        let p = self.params();
        // Short forwarder — the verified helper does the substantive
        // work and provides the ensures we care about. We clone the
        // beneficiary so the helper can take it by value; the clone is
        // a cheap reference-count bump on near-sdk's `AccountId`.
        verified_claim(self.beneficiary.clone(), &p, &mut self.claimed)
    }

    fn params(&self) -> Params {
        Params {
            start:          self.start,
            cliff_duration: self.cliff_duration,
            vest_duration:  self.vest_duration,
            total:          self.total,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use near_sdk::test_utils::VMContextBuilder;
    use near_sdk::testing_env;

    fn acct(s: &str) -> AccountId { s.parse().unwrap() }

    /// NEAR's `block_timestamp` is in nanoseconds; `block_timestamp_ms`
    /// divides by 1_000_000. The test VM lets us set the ns value
    /// directly, so we convert.
    fn ns_for_ms(ms: u64) -> u64 { ms * 1_000_000 }

    /// Build a context for `caller` at wall-clock time `now_ms`.
    fn ctx_at(caller: &AccountId, now_ms: u64) {
        let mut ctx = VMContextBuilder::new();
        ctx.predecessor_account_id(caller.clone())
           .block_timestamp(ns_for_ms(now_ms));
        testing_env!(ctx.build());
    }

    /// Standard fixture: beneficiary "ben.near", start=1000ms, cliff=500ms,
    /// vest=2000ms, total=1_000_000 units. End of vest at t=3000.
    fn setup() -> (AccountId, Vesting) {
        let admin = acct("admin.near");
        ctx_at(&admin, 0);
        let ben = acct("ben.near");
        let v = Vesting::new(ben.clone(), 1_000, 500, 2_000, 1_000_000);
        (ben, v)
    }

    #[test]
    fn init_state_is_well_formed() {
        let (ben, v) = setup();
        assert_eq!(v.beneficiary(), ben);
        assert_eq!(v.total(), 1_000_000);
        assert_eq!(v.claimed_amount(), 0);
    }

    #[test]
    #[should_panic(expected = "vest_duration must be > 0")]
    fn init_rejects_zero_vest_duration() {
        ctx_at(&acct("admin.near"), 0);
        let _ = Vesting::new(acct("ben.near"), 0, 0, 0, 1_000_000);
    }

    #[test]
    #[should_panic(expected = "cliff_duration must be <= vest_duration")]
    fn init_rejects_cliff_longer_than_vest() {
        ctx_at(&acct("admin.near"), 0);
        let _ = Vesting::new(acct("ben.near"), 0, 5_000, 1_000, 1_000_000);
    }

    #[test]
    fn pre_cliff_nothing_vested() {
        let (ben, v) = setup();
        // start=1000, cliff_duration=500 ==> cliff_time=1500.
        // At t=1499 nothing should be vested.
        ctx_at(&ben, 1_499);
        assert_eq!(v.vested_now(), 0);
        assert_eq!(v.claimable_now(), 0);
    }

    #[test]
    fn pre_start_nothing_vested() {
        let (ben, v) = setup();
        // Before `start` itself: trivially pre-cliff.
        ctx_at(&ben, 500);
        assert_eq!(v.vested_now(), 0);
    }

    #[test]
    fn at_cliff_proportional_amount_vested() {
        let (ben, v) = setup();
        // cliff_time = 1_500; elapsed = 500; vest_duration = 2000.
        // vested = 1_000_000 * 500 / 2_000 = 250_000.
        ctx_at(&ben, 1_500);
        assert_eq!(v.vested_now(), 250_000);
        assert_eq!(v.claimable_now(), 250_000);
    }

    #[test]
    fn mid_vest_linear_proportional_amount() {
        let (ben, v) = setup();
        // Halfway through the vest: elapsed=1000, vested=500_000.
        ctx_at(&ben, 2_000);
        assert_eq!(v.vested_now(), 500_000);
    }

    #[test]
    fn end_of_vest_full_amount() {
        let (ben, v) = setup();
        // start + vest_duration = 3000.
        ctx_at(&ben, 3_000);
        assert_eq!(v.vested_now(), 1_000_000);
    }

    #[test]
    fn post_end_caps_at_total() {
        let (ben, v) = setup();
        // Way past the end; still capped at total. Picked well below
        // `u64::MAX / 1_000_000` so the ns conversion in `ctx_at`
        // doesn't overflow the test VM's u64 timestamp.
        ctx_at(&ben, 1_000_000_000_000);
        assert_eq!(v.vested_now(), 1_000_000);
    }

    #[test]
    fn claim_at_cliff_returns_quarter_grant() {
        let (ben, mut v) = setup();
        ctx_at(&ben, 1_500);
        let released = v.claim();
        assert_eq!(released, 250_000);
        assert_eq!(v.claimed_amount(), 250_000);
        // Immediately re-claiming at the same time yields 0 — idempotent
        // in a single block.
        let released_again = v.claim();
        assert_eq!(released_again, 0);
        assert_eq!(v.claimed_amount(), 250_000);
    }

    #[test]
    fn claim_pre_cliff_returns_zero() {
        let (ben, mut v) = setup();
        ctx_at(&ben, 1_000);
        let released = v.claim();
        assert_eq!(released, 0);
        assert_eq!(v.claimed_amount(), 0);
    }

    #[test]
    fn claim_monotonic_across_two_blocks() {
        let (ben, mut v) = setup();
        // Block 1: claim at t=2000 — should get 500_000.
        ctx_at(&ben, 2_000);
        let r1 = v.claim();
        assert_eq!(r1, 500_000);
        // Block 2: claim at t=3000 — should get the remaining 500_000.
        ctx_at(&ben, 3_000);
        let r2 = v.claim();
        assert_eq!(r2, 500_000);
        assert_eq!(v.claimed_amount(), 1_000_000);
        // Sum equals total: nothing dropped, nothing duplicated.
        assert_eq!(r1 + r2, v.total());
    }

    #[test]
    fn claim_post_end_full_remainder() {
        let (ben, mut v) = setup();
        ctx_at(&ben, 10_000);
        let released = v.claim();
        assert_eq!(released, 1_000_000);
        // Re-claim past end: nothing more available.
        let released2 = v.claim();
        assert_eq!(released2, 0);
    }

    #[test]
    #[should_panic(expected = "unauthorized")]
    fn claim_rejects_non_beneficiary() {
        let (_ben, mut v) = setup();
        ctx_at(&acct("attacker.near"), 2_000);
        let _ = v.claim();
    }
}
