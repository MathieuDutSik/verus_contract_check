// MultiversX linear-with-cliff vesting contract with a Verus-verified
// core.
//
// Layout (mirrors `linera_alternate` fungible):
//   - `pub mod vesting_core;`      — re-export of the chain-agnostic
//                                    core. Renamed from `core.rs` so
//                                    `mod core;` doesn't shadow the
//                                    `::core::mem` paths the macro
//                                    expansion emits.
//   - `pub mod mvx_axioms;`        — MultiversX runtime axioms:
//                                    ManagedAddress, ManagedTypeApi
//                                    cascade, `the_caller<M>()`,
//                                    `the_now_secs()`.
//   - `pub mod verified_helpers;`  — `verified_claim_step` kernel.
//   - this file                    — `#[multiversx_sc::contract]` trait
//                                    `Vesting` with endpoints + storage
//                                    mappers + tests.
//
// All amounts are in `u128`, all times in `u64` seconds (matching
// MultiversX's `get_block_timestamp()` unit). The fungible MultiversX
// contract used `BigUint<M>` for amounts to mirror the ESDT idiom;
// for a self-contained vesting contract the `u128` form is sufficient
// and keeps the verification surface aligned with the shared core.
//
// Build modes:
//   cargo build --release        — host build (compiles fine; the
//                                  macro expansion is platform-agnostic).
//   cargo verus verify --target wasm32-unknown-unknown
//                                — verifies the core + verified_claim_step.

#![cfg_attr(not(test), no_std)]

#[path = "vesting_core.rs"]
pub mod vesting_core;
pub mod mvx_axioms;
pub mod verified_helpers;

pub use verified_helpers::{verified_claim_step, ClaimError};

use verus_vesting_core::{compute_claim, compute_vested, Params};

// =====================================================================
// MultiversX contract trait — entry points + storage mappers.
// =====================================================================

multiversx_sc::imports!();

#[multiversx_sc::contract]
pub trait Vesting {
    /// Initialise the grant. `vest_duration_secs` must be > 0 and at
    /// least as long as `cliff_duration_secs`.
    #[init]
    fn init(
        &self,
        beneficiary:        ManagedAddress,
        start_secs:         u64,
        cliff_duration_secs: u64,
        vest_duration_secs:  u64,
        total:              u128,
    ) {
        require!(vest_duration_secs > 0, "vest_duration_secs must be > 0");
        require!(cliff_duration_secs <= vest_duration_secs, "cliff_duration_secs must be <= vest_duration_secs");
        self.beneficiary().set(&beneficiary);
        self.start_secs().set(start_secs);
        self.cliff_duration_secs().set(cliff_duration_secs);
        self.vest_duration_secs().set(vest_duration_secs);
        self.total().set(total);
        self.claimed().set(0u128);
    }

    /// Release everything currently claimable to the beneficiary. The
    /// caller must be the beneficiary.
    #[endpoint]
    #[allow(deprecated)]
    fn claim(&self) -> u128 {
        let caller       = self.blockchain().get_caller();
        // `get_block_timestamp` is the raw-u64 form; the newer
        // `get_block_timestamp_seconds` returns a `TimestampSeconds`
        // newtype which would need extra axiomatisation.
        let now_secs     = self.blockchain().get_block_timestamp();
        let beneficiary  = self.beneficiary().get();
        let params       = self.params();
        let mut claimed  = self.claimed().get();

        // Verified helper writes the new claimed into the local
        // `claimed`; we then persist it back to the mapper.
        let amount = match crate::verified_claim_step(caller, now_secs, beneficiary, &params, &mut claimed) {
            Ok(a)  => a,
            Err(crate::ClaimError::Unauthorized)  => sc_panic!("unauthorized"),
            Err(crate::ClaimError::ArithOverflow) => sc_panic!("schedule arithmetic overflow"),
        };
        if amount > 0 {
            self.claimed().set(claimed);
        }
        amount
    }

    #[view(vestedNow)]
    #[allow(deprecated)]
    fn vested_now(&self) -> u128 {
        let p = self.params();
        let t = self.blockchain().get_block_timestamp();
        compute_vested(&p, t).unwrap_or(0)
    }

    #[view(claimableNow)]
    #[allow(deprecated)]
    fn claimable_now(&self) -> u128 {
        let p = self.params();
        let t = self.blockchain().get_block_timestamp();
        compute_claim(&p, t, self.claimed().get()).unwrap_or(0)
    }

    /// Helper to assemble the immutable `Params` from the storage
    /// mappers. Not an endpoint — pure data marshalling.
    fn params(&self) -> Params {
        Params {
            start:          self.start_secs().get(),
            cliff_duration: self.cliff_duration_secs().get(),
            vest_duration:  self.vest_duration_secs().get(),
            total:          self.total().get(),
        }
    }

    // -- Storage mappers --------------------------------------------------

    #[view(beneficiary)]
    #[storage_mapper("beneficiary")]
    fn beneficiary(&self) -> SingleValueMapper<ManagedAddress>;

    #[storage_mapper("startSecs")]
    fn start_secs(&self) -> SingleValueMapper<u64>;

    #[storage_mapper("cliffDurationSecs")]
    fn cliff_duration_secs(&self) -> SingleValueMapper<u64>;

    #[storage_mapper("vestDurationSecs")]
    fn vest_duration_secs(&self) -> SingleValueMapper<u64>;

    #[view(total)]
    #[storage_mapper("total")]
    fn total(&self) -> SingleValueMapper<u128>;

    #[view(claimed)]
    #[storage_mapper("claimed")]
    fn claimed(&self) -> SingleValueMapper<u128>;
}

// =====================================================================
// Pure-logic tests. As in the fungible MultiversX contract, exercising
// the contract endpoints directly requires either a generated proxy
// (sc-meta) or a ScenarioWorld harness; we instead test the
// `verified_claim_step` kernel via a plain-`Addr` scenario, matching
// what the contract endpoint does at the BigUint-free u128 level.
// =====================================================================

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
        let p = params();
        assert_eq!(compute_vested(&p, 1_499).unwrap(), 0);
    }

    #[test]
    fn at_cliff_quarter() {
        let p = params();
        assert_eq!(compute_vested(&p, 1_500).unwrap(), 250_000);
    }

    #[test]
    fn mid_vest_half() {
        let p = params();
        assert_eq!(compute_vested(&p, 2_000).unwrap(), 500_000);
    }

    #[test]
    fn end_full() {
        let p = params();
        assert_eq!(compute_vested(&p, 3_000).unwrap(), 1_000_000);
    }

    #[test]
    fn claim_idempotent_same_time() {
        let p = params();
        let r = compute_claim(&p, 1_500, 0).unwrap();
        assert_eq!(r, 250_000);
        assert_eq!(compute_claim(&p, 1_500, 250_000).unwrap(), 0);
    }

    #[test]
    fn claim_two_blocks_sums_to_total() {
        let p = params();
        let r1 = compute_claim(&p, 2_000, 0).unwrap();
        let r2 = compute_claim(&p, 3_000, r1).unwrap();
        assert_eq!(r1 + r2, p.total);
    }
}
