// ink! linear-with-cliff vesting contract with a Verus-verified core.
//
// `#[ink::contract]` decorates an entire module — the macro expansion
// produces wasm bindings, ABI marshalling, and dispatch code that
// Verus can't parse. So the verified helpers live *outside* the
// `#[ink::contract]` module, operating on plain values. The contract
// module reads from `#[ink(storage)]` fields, calls `Self::env()` for
// runtime info, and forwards to the verified helpers.
//
// Caller and time are *parameters* to the verified helper (set inside
// the contract method via `self.env().caller()` and
// `self.env().block_timestamp()`). No ghost `the_caller()` / `the_now()`
// is needed for ink! — same simplification as CosmWasm where
// `info.sender` and `env.block.time` are method parameters.
//
// Build modes:
//   cargo build --release --no-default-features --target wasm32-unknown-unknown
//                        — deploy artifact (no_std).
//   cargo test           — runs the unit tests (host, std feature).
//   cargo verus verify --target wasm32-unknown-unknown
//                        — verifies the core + verified_claim_step.

#![cfg_attr(not(feature = "std"), no_std, no_main)]

// Chain-agnostic verified core (Layer 1): schedule + State<A> +
// monotonicity lemmas. Lives outside the `#[ink::contract]` module so
// Verus can see it.
pub mod core;

use ink::primitives::AccountId;
use verus_vesting_core::{compute_claim, Params};

// =====================================================================
// Verified helpers (Layer 2, outside the #[ink::contract] module)
// =====================================================================

vstd::prelude::verus! {
    #[cfg(verus_only)]
    use vstd::prelude::*;
    #[cfg(verus_only)]
    use crate::core::{
        State as CoreState, claimable_at, lemma_vested_bounded, state_after_claim,
    };

    // ink's AccountId is `pub struct AccountId(pub [u8; 32])` —
    // axiomatised here so we can compare caller and beneficiary in the
    // verified helper. Adding the spec is straightforward: the type
    // wraps an array, no transitive generic types to worry about.
    #[verifier::external_type_specification]
    #[verifier::external_body]
    pub struct ExAccountId(#[allow(dead_code)] AccountId);

    pub assume_specification
        [ <AccountId as ::core::cmp::PartialEq>::eq ]
        (a: &AccountId, b: &AccountId) -> (r: bool)
        ensures r == (*a == *b);

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

// =====================================================================
// ink! contract (Layer 3)
// =====================================================================

#[ink::contract]
mod vesting {
    use crate::{verified_claim_step, ClaimError};
    use verus_vesting_core::{compute_claim, compute_vested, Params};

    /// On-chain bundle of vesting state.
    #[ink(storage)]
    pub struct Vesting {
        beneficiary:       AccountId,
        start_ms:          u64,
        cliff_duration_ms: u64,
        vest_duration_ms:  u64,
        total:             Balance,
        claimed:           Balance,
    }

    #[derive(Debug, PartialEq, Eq, scale::Encode, scale::Decode)]
    #[cfg_attr(feature = "std", derive(scale_info::TypeInfo))]
    pub enum Error {
        ZeroVestDuration,
        CliffTooLong,
        Unauthorized,
        ArithOverflow,
    }

    fn map_claim_error(e: ClaimError) -> Error {
        match e {
            ClaimError::Unauthorized  => Error::Unauthorized,
            ClaimError::ArithOverflow => Error::ArithOverflow,
        }
    }

    #[ink(event)]
    pub struct Claimed {
        #[ink(topic)] beneficiary: AccountId,
        amount: Balance,
    }

    impl Vesting {
        #[ink(constructor)]
        pub fn new(
            beneficiary:       AccountId,
            start_ms:          u64,
            cliff_duration_ms: u64,
            vest_duration_ms:  u64,
            total:             Balance,
        ) -> Self {
            if vest_duration_ms == 0 {
                ::core::panic!("vest_duration_ms must be > 0");
            }
            if cliff_duration_ms > vest_duration_ms {
                ::core::panic!("cliff_duration_ms must be <= vest_duration_ms");
            }
            Self {
                beneficiary,
                start_ms,
                cliff_duration_ms,
                vest_duration_ms,
                total,
                claimed: 0,
            }
        }

        #[ink(message)]
        pub fn beneficiary(&self) -> AccountId { self.beneficiary }

        #[ink(message)]
        pub fn total(&self) -> Balance { self.total }

        #[ink(message)]
        pub fn claimed(&self) -> Balance { self.claimed }

        #[ink(message)]
        pub fn vested_now(&self) -> Balance {
            let p = self.params();
            let t = self.env().block_timestamp();
            compute_vested(&p, t).unwrap_or(0)
        }

        #[ink(message)]
        pub fn claimable_now(&self) -> Balance {
            let p = self.params();
            let t = self.env().block_timestamp();
            compute_claim(&p, t, self.claimed).unwrap_or(0)
        }

        #[ink(message)]
        pub fn claim(&mut self) -> Result<Balance, Error> {
            let caller = self.env().caller();
            let now    = self.env().block_timestamp();
            let p      = self.params();
            let amount = verified_claim_step(
                caller, now, self.beneficiary, &p, &mut self.claimed,
            ).map_err(map_claim_error)?;
            if amount > 0 {
                self.env().emit_event(Claimed { beneficiary: self.beneficiary, amount });
            }
            Ok(amount)
        }

        fn params(&self) -> Params {
            Params {
                start:          self.start_ms,
                cliff_duration: self.cliff_duration_ms,
                vest_duration:  self.vest_duration_ms,
                total:          self.total,
            }
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;
        use ink::env::test;

        type AccId = <ink::env::DefaultEnvironment as ink::env::Environment>::AccountId;

        fn accounts() -> test::DefaultAccounts<ink::env::DefaultEnvironment> {
            test::default_accounts::<ink::env::DefaultEnvironment>()
        }

        fn set_caller(caller: AccId) {
            test::set_caller::<ink::env::DefaultEnvironment>(caller);
        }

        fn set_now(now_ms: u64) {
            // ink's block timestamp is u64 ms; the test env stores it
            // directly.
            ink::env::test::set_block_timestamp::<ink::env::DefaultEnvironment>(now_ms);
        }

        /// Standard fixture: beneficiary=bob, start=1000ms, cliff=500ms,
        /// vest=2000ms, total=1_000_000. End at t=3000.
        fn setup() -> (Vesting, test::DefaultAccounts<ink::env::DefaultEnvironment>) {
            let a = accounts();
            set_caller(a.alice);
            let v = Vesting::new(a.bob, 1_000, 500, 2_000, 1_000_000);
            (v, a)
        }

        #[ink::test]
        fn init_state_populated() {
            let (v, a) = setup();
            assert_eq!(v.beneficiary(), a.bob);
            assert_eq!(v.total(), 1_000_000);
            assert_eq!(v.claimed(), 0);
        }

        #[ink::test]
        #[should_panic(expected = "vest_duration_ms must be > 0")]
        fn init_rejects_zero_vest_duration() {
            let a = accounts();
            let _ = Vesting::new(a.bob, 0, 0, 0, 1_000);
        }

        #[ink::test]
        #[should_panic(expected = "cliff_duration_ms must be <= vest_duration_ms")]
        fn init_rejects_cliff_longer_than_vest() {
            let a = accounts();
            let _ = Vesting::new(a.bob, 0, 5_000, 1_000, 1_000);
        }

        #[ink::test]
        fn pre_cliff_nothing_vested() {
            let (v, _) = setup();
            set_now(1_499);
            assert_eq!(v.vested_now(), 0);
            assert_eq!(v.claimable_now(), 0);
        }

        #[ink::test]
        fn at_cliff_proportional() {
            let (v, _) = setup();
            set_now(1_500);
            assert_eq!(v.vested_now(), 250_000);
            assert_eq!(v.claimable_now(), 250_000);
        }

        #[ink::test]
        fn mid_vest_linear() {
            let (v, _) = setup();
            set_now(2_000);
            assert_eq!(v.vested_now(), 500_000);
        }

        #[ink::test]
        fn end_of_vest_full() {
            let (v, _) = setup();
            set_now(3_000);
            assert_eq!(v.vested_now(), 1_000_000);
        }

        #[ink::test]
        fn claim_at_cliff_returns_quarter() {
            let (mut v, a) = setup();
            set_caller(a.bob);
            set_now(1_500);
            let r = v.claim().unwrap();
            assert_eq!(r, 250_000);
            assert_eq!(v.claimed(), 250_000);
        }

        #[ink::test]
        fn claim_idempotent_in_block() {
            let (mut v, a) = setup();
            set_caller(a.bob);
            set_now(1_500);
            v.claim().unwrap();
            let again = v.claim().unwrap();
            assert_eq!(again, 0);
            assert_eq!(v.claimed(), 250_000);
        }

        #[ink::test]
        fn claim_monotonic_two_blocks() {
            let (mut v, a) = setup();
            set_caller(a.bob);
            set_now(2_000);
            let r1 = v.claim().unwrap();
            set_now(3_000);
            let r2 = v.claim().unwrap();
            assert_eq!(r1, 500_000);
            assert_eq!(r2, 500_000);
            assert_eq!(r1 + r2, v.total());
        }

        #[ink::test]
        fn claim_unauthorized_rejected() {
            let (mut v, a) = setup();
            set_caller(a.alice); // alice isn't the beneficiary; bob is
            set_now(2_000);
            assert_eq!(v.claim(), Err(Error::Unauthorized));
            assert_eq!(v.claimed(), 0);
        }

        #[ink::test]
        fn claim_post_end_drains() {
            let (mut v, a) = setup();
            set_caller(a.bob);
            set_now(10_000);
            let r = v.claim().unwrap();
            assert_eq!(r, 1_000_000);
        }
    }
}
