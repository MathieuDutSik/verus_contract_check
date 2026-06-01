// Gear linear-with-cliff vesting contract with a Verus-verified core.
//
// Gear's model is actor-style: each contract is a program that
// receives messages via `handle` and emits replies. State is held in
// a `static mut` between calls. The vesting state is one grant per
// program — no map needed.
//
// Layout:
//   - `pub mod core;`         — chain-agnostic State<A>, schedule,
//                               and monotonicity lemmas (identical to
//                               the other chains).
//   - `pub mod gear_axioms;`  — Gear-specific axioms: ActorId external
//                               type, `source()` and `now_ms()` runtime
//                               wrappers + their ghost projections.
//   - this file               — the contract: `Vesting` struct,
//                               verified `apply_claim` and
//                               `verified_claim` helpers, `init` and
//                               `handle` extern "C" entry points.
//
// `apply_claim` is a unit-testable kernel that takes the sender/time
// as explicit parameters (so unit tests can inject them). The
// runtime-facing `verified_claim` is a thin forwarder that reads
// sender + time via `source()` / `now_ms()` and calls `apply_claim`.
// Same shape as the fungible Gear contract's `apply_transfer` /
// `verified_transfer` pair.

#![cfg_attr(not(test), no_std)]
extern crate alloc;

pub mod core;
pub mod gear_axioms;

use gstd::{msg, prelude::*, ActorId};
use parity_scale_codec::{Decode, Encode};
use scale_info::TypeInfo;

use crate::gear_axioms::{now_ms, source};
use verus_vesting_core::{compute_claim, compute_vested, Params};

#[derive(Encode, Decode, TypeInfo)]
pub struct InitConfig {
    pub beneficiary:       ActorId,
    pub start_ms:          u64,
    pub cliff_duration_ms: u64,
    pub vest_duration_ms:  u64,
    pub total:             u128,
}

#[derive(Encode, Decode, TypeInfo)]
pub enum Action {
    Claim,
    VestedNow,
    ClaimableNow,
    Claimed,
    BeneficiaryQuery,
}

#[derive(Encode, Decode, TypeInfo)]
pub enum Event {
    Claimed       { beneficiary: ActorId, amount: u128 },
    VestedNow     { amount: u128 },
    ClaimableNow  { amount: u128 },
    ClaimedSoFar  { amount: u128 },
    Beneficiary   { who: ActorId },
}

/// Vesting program state. Defined outside `verus!{}` because of the
/// scale codec derives, but the field types are all primitive or
/// already-spec'd (ActorId), so the verified helpers operate on the
/// individual fields rather than the struct as a whole.
#[derive(Default)]
pub struct Vesting {
    pub beneficiary:       Option<ActorId>,
    pub start_ms:          u64,
    pub cliff_duration_ms: u64,
    pub vest_duration_ms:  u64,
    pub total:             u128,
    pub claimed:           u128,
}

impl Vesting {
    pub fn init(cfg: InitConfig) -> Self {
        // Same validation the verified helpers' requires demands.
        if cfg.vest_duration_ms == 0 {
            ::core::panic!("vest_duration_ms must be > 0");
        }
        if cfg.cliff_duration_ms > cfg.vest_duration_ms {
            ::core::panic!("cliff_duration_ms must be <= vest_duration_ms");
        }
        Self {
            beneficiary:       Some(cfg.beneficiary),
            start_ms:          cfg.start_ms,
            cliff_duration_ms: cfg.cliff_duration_ms,
            vest_duration_ms:  cfg.vest_duration_ms,
            total:             cfg.total,
            claimed:           0,
        }
    }

    pub fn params(&self) -> Params {
        Params {
            start:          self.start_ms,
            cliff_duration: self.cliff_duration_ms,
            vest_duration:  self.vest_duration_ms,
            total:          self.total,
        }
    }

    /// Test-only entry point. Production code calls `verified_claim`
    /// (which reads sender + time via the axiomatized `source()` /
    /// `now_ms()`). Tests inject those values and route through the
    /// same kernel.
    pub fn do_claim(&mut self, sender: ActorId, now: u64) -> Result<u128, ClaimError> {
        let beneficiary = self.beneficiary.expect("not initialised");
        let p = self.params();
        apply_claim(sender, now, beneficiary, &p, &mut self.claimed)
    }
}

// =====================================================================
// Verified helpers (inside `verus!{}`)
// =====================================================================

vstd::prelude::verus! {
    #[cfg(verus_only)]
    use vstd::prelude::*;
    #[cfg(verus_only)]
    use crate::core::{
        State as CoreState, claimable_at, lemma_vested_bounded, state_after_claim,
    };
    #[cfg(verus_only)]
    use crate::gear_axioms::{the_sender, the_now_ms};

    /// Errors the verified helpers raise.
    #[derive(PartialEq, Eq, Debug)]
    pub enum ClaimError {
        Unauthorized,
        ArithOverflow,
    }

    /// Verified claim kernel: the substantive logic, taking `sender`
    /// and `now` as explicit parameters so it's shared between the
    /// production path (which reads them from `msg::source()` /
    /// `exec::block_timestamp()`) and the unit-test path.
    ///
    /// `ensures` (success path):
    ///
    ///   - authorisation: `sender == beneficiary`.
    ///   - state-level connection: `*final(claimed) == state_after_claim(
    ///     CoreState { beneficiary, params: *params, claimed: *old(claimed) },
    ///     now ).claimed`.
    ///   - monotonicity: `*final(claimed) >= *old(claimed)`.
    ///   - the returned amount equals the delta in `claimed`.
    pub fn apply_claim(
        sender:      ActorId,
        now:         u64,
        beneficiary: ActorId,
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
                    &&& sender == beneficiary
                    &&& amount as int
                        == (*final(claimed) as int) - (*old(claimed) as int)
                    &&& *final(claimed) as int
                        == state_after_claim::<ActorId>(
                                CoreState {
                                    beneficiary,
                                    params:      *params,
                                    claimed:     *old(claimed),
                                },
                                now,
                           ).claimed as int
                }
                Err(_) => true,
            },
    {
        if !(sender == beneficiary) {
            return Err(ClaimError::Unauthorized);
        }
        let amount = match compute_claim(params, now, *claimed) {
            Ok(a)  => a,
            Err(_) => return Err(ClaimError::ArithOverflow),
        };
        proof {
            lemma_vested_bounded(*params, now);
        }
        if amount > 0 {
            *claimed = *claimed + amount;
        }
        Ok(amount)
    }

    /// Verified claim entry point. Reads the sender via the axiomatised
    /// `source()` and the time via `now_ms()`, then delegates to
    /// `apply_claim`. This is what production `handle()` calls.
    pub fn verified_claim(
        beneficiary: ActorId,
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
                    &&& the_sender() == beneficiary
                    &&& amount as int
                        == (*final(claimed) as int) - (*old(claimed) as int)
                    &&& *final(claimed) as int
                        == state_after_claim::<ActorId>(
                                CoreState {
                                    beneficiary,
                                    params:      *params,
                                    claimed:     *old(claimed),
                                },
                                the_now_ms(),
                           ).claimed as int
                }
                Err(_) => true,
            },
    {
        let sender = source();
        let now    = now_ms();
        apply_claim(sender, now, beneficiary, params, claimed)
    }
}

// =====================================================================
// Gear program glue (unverified): static state, init / handle
// extern "C" entry points.
// =====================================================================

static mut STATE: Option<Vesting> = None;

fn state() -> &'static mut Vesting {
    #[allow(static_mut_refs)]
    unsafe { STATE.as_mut().expect("uninitialized") }
}

#[no_mangle]
extern "C" fn init() {
    let cfg: InitConfig = msg::load().expect("init payload");
    unsafe { STATE = Some(Vesting::init(cfg)); }
}

#[no_mangle]
extern "C" fn handle() {
    let action: Action = msg::load().expect("handle payload");
    let s = state();
    let beneficiary = s.beneficiary.expect("not initialised");
    let p = s.params();
    match action {
        Action::Claim => {
            let amount = match verified_claim(beneficiary, &p, &mut s.claimed) {
                Ok(a)  => a,
                Err(e) => gstd::ext::panic(claim_err_str(e)),
            };
            msg::reply(Event::Claimed { beneficiary, amount }, 0).expect("reply");
        }
        Action::VestedNow => {
            let amount = match compute_vested(&p, gstd::exec::block_timestamp()) {
                Ok(v)  => v,
                Err(e) => gstd::ext::panic(e),
            };
            msg::reply(Event::VestedNow { amount }, 0).expect("reply");
        }
        Action::ClaimableNow => {
            let amount = match compute_claim(&p, gstd::exec::block_timestamp(), s.claimed) {
                Ok(a)  => a,
                Err(e) => gstd::ext::panic(e),
            };
            msg::reply(Event::ClaimableNow { amount }, 0).expect("reply");
        }
        Action::Claimed => {
            msg::reply(Event::ClaimedSoFar { amount: s.claimed }, 0).expect("reply");
        }
        Action::BeneficiaryQuery => {
            msg::reply(Event::Beneficiary { who: beneficiary }, 0).expect("reply");
        }
    }
}

fn claim_err_str(e: ClaimError) -> &'static str {
    match e {
        ClaimError::Unauthorized  => "unauthorized",
        ClaimError::ArithOverflow => "schedule arithmetic overflow",
    }
}

// =====================================================================
// Tests — use `do_claim` to inject sender/now (the production helper
// `verified_claim` reads them from the runtime, which isn't available
// in unit tests). Both paths share the verified `apply_claim` kernel.
// =====================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn id(b: u8) -> ActorId { ActorId::new([b; 32]) }

    fn cfg() -> InitConfig {
        InitConfig {
            beneficiary:       id(1),
            start_ms:          1_000,
            cliff_duration_ms: 500,
            vest_duration_ms:  2_000,
            total:             1_000_000,
        }
    }

    fn setup() -> Vesting { Vesting::init(cfg()) }

    #[test]
    fn init_state_populated() {
        let v = setup();
        assert_eq!(v.beneficiary, Some(id(1)));
        assert_eq!(v.total, 1_000_000);
        assert_eq!(v.claimed, 0);
    }

    #[test]
    #[should_panic(expected = "vest_duration_ms must be > 0")]
    fn init_rejects_zero_vest_duration() {
        let mut c = cfg();
        c.vest_duration_ms = 0;
        let _ = Vesting::init(c);
    }

    #[test]
    #[should_panic(expected = "cliff_duration_ms must be <= vest_duration_ms")]
    fn init_rejects_cliff_longer_than_vest() {
        let mut c = cfg();
        c.cliff_duration_ms = 5_000;
        c.vest_duration_ms  = 1_000;
        let _ = Vesting::init(c);
    }

    #[test]
    fn pre_cliff_nothing_claimable() {
        let mut v = setup();
        let r = v.do_claim(id(1), 1_499).unwrap();
        assert_eq!(r, 0);
        assert_eq!(v.claimed, 0);
    }

    #[test]
    fn at_cliff_quarter_released() {
        let mut v = setup();
        let r = v.do_claim(id(1), 1_500).unwrap();
        assert_eq!(r, 250_000);
        assert_eq!(v.claimed, 250_000);
    }

    #[test]
    fn mid_vest_linear() {
        let mut v = setup();
        let r = v.do_claim(id(1), 2_000).unwrap();
        assert_eq!(r, 500_000);
    }

    #[test]
    fn post_end_full_release() {
        let mut v = setup();
        let r = v.do_claim(id(1), 10_000).unwrap();
        assert_eq!(r, 1_000_000);
        let again = v.do_claim(id(1), 10_000).unwrap();
        assert_eq!(again, 0);
    }

    #[test]
    fn monotonic_two_block_claim() {
        let mut v = setup();
        let r1 = v.do_claim(id(1), 2_000).unwrap();
        let r2 = v.do_claim(id(1), 3_000).unwrap();
        assert_eq!(r1, 500_000);
        assert_eq!(r2, 500_000);
        assert_eq!(r1 + r2, v.total);
    }

    #[test]
    fn unauthorized_rejected() {
        let mut v = setup();
        assert_eq!(v.do_claim(id(99), 2_000), Err(ClaimError::Unauthorized));
        assert_eq!(v.claimed, 0);
    }

    #[test]
    fn idempotent_in_same_block() {
        let mut v = setup();
        let r1 = v.do_claim(id(1), 1_500).unwrap();
        let r2 = v.do_claim(id(1), 1_500).unwrap();
        assert_eq!(r1, 250_000);
        assert_eq!(r2, 0);
        assert_eq!(v.claimed, 250_000);
    }
}
