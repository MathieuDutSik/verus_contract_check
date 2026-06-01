// Solana vesting program with Verus-verified arithmetic + claim
// authorisation.
//
// Solana's data model: state lives in account-data buffers, not in
// per-instance struct state. The vesting account holds the full
// `VestingAccount` record (beneficiary, schedule, claimed). The
// program serialises/deserialises the buffer via Borsh, and treats the
// `is_signer` flag on `AccountInfo` as the authorisation source.
//
// We factor the work into:
//   - Layer 1 (`core.rs`): chain-agnostic State<A> + schedule lemmas.
//   - Layer 2 (`apply_*` inside `verus!{}`): pure-data updates on the
//     `VestingAccount`, with `ensures` proving:
//        * `apply_init_vesting`: initial bundle is set correctly.
//        * `apply_claim`: auth (signer == beneficiary), monotonicity,
//          and the state-level connection to `state_after_claim`.
//   - Layer 3 (entry-point `process_instruction`): unverified glue —
//     parses positional accounts, deserialises buffers, fetches the
//     Clock sysvar, calls the verified apply_*, reserialises.
//
// Time. The chain time is `Clock::unix_timestamp: i64` (seconds since
// the unix epoch). We axiomatise it via `the_now_secs()` ghost that
// returns a `u64` (the i64-as-u64 cast of unix_timestamp, clamped to
// 0 for pre-epoch times). The schedule downstream is in seconds.

pub mod core;

use borsh::{BorshDeserialize, BorshSerialize};
use solana_program::{
    account_info::AccountInfo,
    entrypoint,
    entrypoint::ProgramResult,
    program_error::ProgramError,
    pubkey::Pubkey,
    sysvar::{clock::Clock, Sysvar},
};

use verus_vesting_core::Params;

vstd::prelude::verus! {
    // External types from solana_program — opaque to Verus.
    #[verifier::external_type_specification]
    #[verifier::external_body]
    pub struct ExPubkey(#[allow(dead_code)] Pubkey);

    #[verifier::external_type_specification]
    #[verifier::external_body]
    pub struct ExAccountInfo<'a>(#[allow(dead_code)] AccountInfo<'a>);

    /// Verus-friendly error enum returned by `apply_*` helpers.
    #[derive(Debug, PartialEq, Eq)]
    pub enum VestingError {
        AlreadyInitialized,
        NotInitialized,
        Unauthorized,
        ZeroVestDuration,
        CliffTooLong,
        ArithOverflow,
        InvalidArgument,
        MissingSignature,
        DeserializationFailed,
    }

    // Equality on Pubkey.
    pub assume_specification
        [ <Pubkey as ::core::cmp::PartialEq>::eq ]
        (a: &Pubkey, b: &Pubkey) -> (r: bool)
        ensures r == (*a == *b);

    // -- Ghost views of AccountInfo state ----------------------------------

    pub uninterp spec fn ai_signed<'a>(a: &AccountInfo<'a>) -> bool;
    pub uninterp spec fn ai_key<'a>(a: &AccountInfo<'a>) -> Pubkey;
    pub uninterp spec fn ai_vesting_data<'a>(a: &AccountInfo<'a>) -> VestingAccount;

    /// The ghost wall-clock time in seconds since the unix epoch.
    /// The Solana runtime gives us `Clock::unix_timestamp` as an `i64`;
    /// pre-epoch times are not meaningful for a vesting schedule, so we
    /// cast to `u64` (negative → wraps to a large value; the schedule's
    /// `t < start + cliff_duration` branch absorbs this honestly).
    pub uninterp spec fn the_now_secs() -> u64;

    // -- AccountInfo accessor axioms ---------------------------------------

    #[verifier::external_body]
    pub fn read_is_signer<'a>(a: &AccountInfo<'a>) -> (r: bool)
        ensures r == ai_signed(a),
    {
        a.is_signer
    }

    #[verifier::external_body]
    pub fn read_key<'a>(a: &AccountInfo<'a>) -> (r: Pubkey)
        ensures r == ai_key(a),
    {
        *a.key
    }

    #[verifier::external_body]
    pub fn read_vesting_data<'a>(a: &AccountInfo<'a>) -> (r: Result<VestingAccount, VestingError>)
        ensures
            match r {
                Ok(td) => td == ai_vesting_data(a),
                Err(_) => true,
            },
    {
        #[cfg(not(verus_only))]
        return VestingAccount::try_from_slice(&a.data.borrow())
            .map_err(|_| VestingError::DeserializationFailed);
        #[cfg(verus_only)]
        Err(VestingError::DeserializationFailed)
    }

    #[verifier::external_body]
    pub fn write_vesting_data<'a>(a: &AccountInfo<'a>, data: &VestingAccount) -> (r: Result<(), VestingError>)
        ensures
            match r {
                Ok(()) => ai_vesting_data(a) == *data,
                Err(_) => true,
            },
    {
        #[cfg(not(verus_only))]
        return data.serialize(&mut &mut a.data.borrow_mut()[..])
            .map_err(|_| VestingError::DeserializationFailed);
        #[cfg(verus_only)]
        Err(VestingError::DeserializationFailed)
    }

    /// Read the current Clock sysvar. Returns `the_now_secs()` (a u64,
    /// the i64-as-u64 cast of `unix_timestamp`).
    #[verifier::external_body]
    pub fn read_now_secs() -> (r: u64)
        ensures r == the_now_secs(),
    {
        #[cfg(not(verus_only))]
        return Clock::get().unwrap().unix_timestamp.max(0) as u64;
        #[cfg(verus_only)]
        0
    }

    /// The vesting account record. Note the `#[cfg]` gate on Borsh —
    /// the derives produce code that Verus's lifetime erasure tripped on
    /// in some earlier attempts; cfg-gating them keeps Verus happy
    /// without losing runtime serialisation.
    #[cfg_attr(not(verus_only), derive(BorshSerialize, BorshDeserialize))]
    #[derive(Debug, Default, PartialEq, Eq)]
    pub struct VestingAccount {
        pub initialized:         bool,
        pub beneficiary:         Pubkey,
        pub start_secs:          u64,
        pub cliff_duration_secs: u64,
        pub vest_duration_secs:  u64,
        pub total:               u128,
        pub claimed:             u128,
    }
}

#[cfg_attr(not(verus_only), derive(BorshSerialize, BorshDeserialize))]
#[derive(Debug)]
pub enum Instruction {
    Init {
        beneficiary:         Pubkey,
        start_secs:          u64,
        cliff_duration_secs: u64,
        vest_duration_secs:  u64,
        total:               u128,
    },
    Claim,
}

#[cfg(not(verus_only))]
entrypoint!(process_instruction);

#[cfg(not(verus_only))]
pub fn process_instruction<'a>(
    _program_id: &Pubkey,
    accounts: &'a [AccountInfo<'a>],
    data: &[u8],
) -> ProgramResult {
    let instruction = Instruction::try_from_slice(data)
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    match instruction {
        Instruction::Init { beneficiary, start_secs, cliff_duration_secs, vest_duration_secs, total } =>
            verified_init_instruction(accounts, beneficiary, start_secs, cliff_duration_secs, vest_duration_secs, total)
                .map_err(map_vesting_error),
        Instruction::Claim =>
            verified_claim_instruction(accounts)
                .map(|_| ())
                .map_err(map_vesting_error),
    }
}

#[cfg(not(verus_only))]
fn map_vesting_error(e: VestingError) -> ProgramError {
    match e {
        VestingError::AlreadyInitialized    => ProgramError::AccountAlreadyInitialized,
        VestingError::NotInitialized        => ProgramError::UninitializedAccount,
        VestingError::Unauthorized          => ProgramError::MissingRequiredSignature,
        VestingError::ZeroVestDuration      => ProgramError::InvalidArgument,
        VestingError::CliffTooLong          => ProgramError::InvalidArgument,
        VestingError::ArithOverflow         => ProgramError::ArithmeticOverflow,
        VestingError::InvalidArgument       => ProgramError::InvalidArgument,
        VestingError::MissingSignature      => ProgramError::MissingRequiredSignature,
        VestingError::DeserializationFailed => ProgramError::InvalidAccountData,
    }
}

// =====================================================================
// Verified apply_* helpers
// =====================================================================

vstd::prelude::verus! {
    #[cfg(verus_only)]
    use vstd::prelude::*;
    #[cfg(verus_only)]
    use crate::core::{
        State as CoreState, claimable_at, lemma_vested_bounded, state_after_claim,
    };

    /// Initialise the vesting account. The caller is expected to have
    /// validated `vest_duration_secs > 0` and `cliff_duration_secs <=
    /// vest_duration_secs` (we *require* them).
    pub fn apply_init_vesting(
        acc:                 &mut VestingAccount,
        beneficiary:         Pubkey,
        start_secs:          u64,
        cliff_duration_secs: u64,
        vest_duration_secs:  u64,
        total:               u128,
    ) -> (r: Result<(), VestingError>)
        requires
            vest_duration_secs > 0,
            cliff_duration_secs <= vest_duration_secs,
        ensures
            match r {
                Ok(()) =>
                    !old(acc).initialized
                    && final(acc).initialized
                    && final(acc).beneficiary         == beneficiary
                    && final(acc).start_secs          == start_secs
                    && final(acc).cliff_duration_secs == cliff_duration_secs
                    && final(acc).vest_duration_secs  == vest_duration_secs
                    && final(acc).total               == total
                    && final(acc).claimed             == 0u128,
                Err(_) => true,
            },
    {
        if acc.initialized { return Err(VestingError::AlreadyInitialized); }
        acc.initialized         = true;
        acc.beneficiary         = beneficiary;
        acc.start_secs          = start_secs;
        acc.cliff_duration_secs = cliff_duration_secs;
        acc.vest_duration_secs  = vest_duration_secs;
        acc.total               = total;
        acc.claimed             = 0;
        Ok(())
    }

    /// Verified claim step. Updates the account's `claimed` field with
    /// the schedule's claimable amount at `now_secs`; rejects if the
    /// signer's key isn't the registered beneficiary.
    ///
    /// `ensures` (success path):
    ///   - the account was initialised.
    ///   - `signer_key == acc.beneficiary`.
    ///   - the immutable schedule fields are preserved.
    ///   - `final(acc).claimed >= old(acc).claimed` (monotonic).
    ///   - `returned amount == final.claimed - old.claimed`.
    ///   - state-level connection: `final.claimed == state_after_claim
    ///     (CoreState { beneficiary, params, claimed: old.claimed },
    ///      now_secs).claimed`.
    pub fn apply_claim(
        acc:        &mut VestingAccount,
        signer_key: Pubkey,
        now_secs:   u64,
    ) -> (r: Result<u128, VestingError>)
        requires
            old(acc).initialized,
            old(acc).vest_duration_secs > 0,
            old(acc).cliff_duration_secs <= old(acc).vest_duration_secs,
            (old(acc).claimed as nat) <= (old(acc).total as nat),
        ensures
            // Immutable fields preserved.
            final(acc).initialized         == old(acc).initialized,
            final(acc).beneficiary         == old(acc).beneficiary,
            final(acc).start_secs          == old(acc).start_secs,
            final(acc).cliff_duration_secs == old(acc).cliff_duration_secs,
            final(acc).vest_duration_secs  == old(acc).vest_duration_secs,
            final(acc).total               == old(acc).total,
            // Monotonic claimed.
            final(acc).claimed >= old(acc).claimed,
            match r {
                Ok(amount) => {
                    &&& old(acc).initialized
                    &&& signer_key == old(acc).beneficiary
                    &&& amount as int == (final(acc).claimed as int) - (old(acc).claimed as int)
                    &&& final(acc).claimed as int
                        == state_after_claim::<Pubkey>(
                                CoreState {
                                    beneficiary: old(acc).beneficiary,
                                    params:      Params {
                                        start:          old(acc).start_secs,
                                        cliff_duration: old(acc).cliff_duration_secs,
                                        vest_duration:  old(acc).vest_duration_secs,
                                        total:          old(acc).total,
                                    },
                                    claimed:     old(acc).claimed,
                                },
                                now_secs,
                           ).claimed as int
                }
                Err(_) => true,
            },
    {
        if !acc.initialized { return Err(VestingError::NotInitialized); }
        if signer_key != acc.beneficiary { return Err(VestingError::Unauthorized); }
        let params = Params {
            start:          acc.start_secs,
            cliff_duration: acc.cliff_duration_secs,
            vest_duration:  acc.vest_duration_secs,
            total:          acc.total,
        };
        let amount = match verus_vesting_core::compute_claim(&params, now_secs, acc.claimed) {
            Ok(a)  => a,
            Err(_) => return Err(VestingError::ArithOverflow),
        };
        proof {
            lemma_vested_bounded(params, now_secs);
        }
        if amount > 0 {
            acc.claimed = acc.claimed + amount;
        }
        Ok(amount)
    }

    // -- End-to-end verified instructions ----------------------------------

    /// End-to-end Init: parse positional accounts, signer check, init
    /// args validation, deserialise the (empty) vesting account, call
    /// `apply_init_vesting`, write back.
    ///
    /// Positional convention:
    ///   accounts[0]: payer (must be a signer)
    ///   accounts[1]: vesting account to initialise (mutable buffer)
    pub fn verified_init_instruction<'a>(
        accounts:            &'a [AccountInfo<'a>],
        beneficiary:         Pubkey,
        start_secs:          u64,
        cliff_duration_secs: u64,
        vest_duration_secs:  u64,
        total:               u128,
    ) -> (r: Result<(), VestingError>)
        ensures
            match r {
                Ok(()) => accounts.len() >= 2 && ai_signed(&accounts[0]),
                Err(_) => true,
            },
    {
        if accounts.len() < 2 { return Err(VestingError::InvalidArgument); }
        let payer   = &accounts[0];
        let vesting = &accounts[1];
        if !read_is_signer(payer) { return Err(VestingError::MissingSignature); }

        // Init-arg validation (matches apply_init_vesting's requires).
        if vest_duration_secs == 0 { return Err(VestingError::ZeroVestDuration); }
        if cliff_duration_secs > vest_duration_secs { return Err(VestingError::CliffTooLong); }

        let mut acc = match read_vesting_data(vesting) {
            Ok(d)  => d,
            Err(e) => return Err(e),
        };
        match apply_init_vesting(
            &mut acc, beneficiary, start_secs, cliff_duration_secs,
            vest_duration_secs, total,
        ) {
            Ok(())  => {}
            Err(e)  => return Err(e),
        }
        match write_vesting_data(vesting, &acc) {
            Ok(())  => Ok(()),
            Err(e)  => Err(e),
        }
    }

    /// End-to-end Claim: parse positional accounts, signer check, fetch
    /// time from Clock sysvar, call `apply_claim`, write back.
    ///
    /// Positional convention:
    ///   accounts[0]: beneficiary (must be a signer; key checked
    ///                inside apply_claim against acc.beneficiary)
    ///   accounts[1]: vesting account (mutable buffer)
    ///
    /// `ensures` (success path):
    ///   - accounts.len() >= 2 and accounts[0] is a signer.
    ///   - (The substantive properties — auth, monotonicity, schedule
    ///     correctness — are pinned by `apply_claim`'s ensures on the
    ///     local `acc` value; we don't restate them at the dispatch
    ///     level for the same framing reason as the fungible Solana
    ///     contract, see TODO.md.)
    pub fn verified_claim_instruction<'a>(
        accounts: &'a [AccountInfo<'a>],
    ) -> (r: Result<u128, VestingError>)
        ensures
            match r {
                Ok(_)  => accounts.len() >= 2 && ai_signed(&accounts[0]),
                Err(_) => true,
            },
    {
        if accounts.len() < 2 { return Err(VestingError::InvalidArgument); }
        let signer  = &accounts[0];
        let vesting = &accounts[1];
        if !read_is_signer(signer) { return Err(VestingError::MissingSignature); }
        let signer_key = read_key(signer);

        let mut acc = match read_vesting_data(vesting) {
            Ok(d)  => d,
            Err(e) => return Err(e),
        };
        // The verified-init path establishes `acc.initialized` and the
        // schedule's well-formedness; we must restate them at runtime
        // because Verus can't carry that across the Borsh read.
        if !acc.initialized { return Err(VestingError::NotInitialized); }
        if acc.vest_duration_secs == 0 { return Err(VestingError::ZeroVestDuration); }
        if acc.cliff_duration_secs > acc.vest_duration_secs { return Err(VestingError::CliffTooLong); }
        if acc.claimed > acc.total { return Err(VestingError::InvalidArgument); }

        let now_secs = read_now_secs();
        let amount = match apply_claim(&mut acc, signer_key, now_secs) {
            Ok(a)  => a,
            Err(e) => return Err(e),
        };
        match write_vesting_data(vesting, &acc) {
            Ok(())  => Ok(amount),
            Err(e)  => Err(e),
        }
    }
}

// =====================================================================
// Tests — exercise the `apply_*` helpers directly. The instruction-
// level glue (AccountInfo, Borsh, Clock) requires either solana-test or
// a real account harness, which we don't pull in.
// =====================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn key(b: u8) -> Pubkey { Pubkey::new_from_array([b; 32]) }

    fn init_acc(now_supply: u128) -> VestingAccount {
        let mut acc = VestingAccount::default();
        apply_init_vesting(&mut acc, key(1), 1_000, 500, 2_000, now_supply).unwrap();
        acc
    }

    #[test]
    fn init_populates_account() {
        let acc = init_acc(1_000_000);
        assert!(acc.initialized);
        assert_eq!(acc.beneficiary, key(1));
        assert_eq!(acc.total, 1_000_000);
        assert_eq!(acc.claimed, 0);
        assert_eq!(acc.start_secs, 1_000);
        assert_eq!(acc.cliff_duration_secs, 500);
        assert_eq!(acc.vest_duration_secs, 2_000);
    }

    #[test]
    fn init_twice_rejected() {
        let mut acc = init_acc(1_000_000);
        assert_eq!(
            apply_init_vesting(&mut acc, key(2), 0, 0, 1_000, 500),
            Err(VestingError::AlreadyInitialized),
        );
    }

    #[test]
    fn pre_cliff_claim_returns_zero() {
        let mut acc = init_acc(1_000_000);
        let r = apply_claim(&mut acc, key(1), 1_499).unwrap();
        assert_eq!(r, 0);
        assert_eq!(acc.claimed, 0);
    }

    #[test]
    fn at_cliff_claim_returns_quarter() {
        let mut acc = init_acc(1_000_000);
        let r = apply_claim(&mut acc, key(1), 1_500).unwrap();
        assert_eq!(r, 250_000);
        assert_eq!(acc.claimed, 250_000);
    }

    #[test]
    fn mid_vest_returns_half() {
        let mut acc = init_acc(1_000_000);
        let r = apply_claim(&mut acc, key(1), 2_000).unwrap();
        assert_eq!(r, 500_000);
    }

    #[test]
    fn post_end_returns_remainder_then_idempotent() {
        let mut acc = init_acc(1_000_000);
        let r = apply_claim(&mut acc, key(1), 10_000).unwrap();
        assert_eq!(r, 1_000_000);
        let again = apply_claim(&mut acc, key(1), 10_000).unwrap();
        assert_eq!(again, 0);
    }

    #[test]
    fn monotonic_two_block_claim() {
        let mut acc = init_acc(1_000_000);
        let r1 = apply_claim(&mut acc, key(1), 2_000).unwrap();
        let r2 = apply_claim(&mut acc, key(1), 3_000).unwrap();
        assert_eq!(r1, 500_000);
        assert_eq!(r2, 500_000);
        assert_eq!(r1 + r2, acc.total);
    }

    #[test]
    fn unauthorized_signer_rejected() {
        let mut acc = init_acc(1_000_000);
        assert_eq!(
            apply_claim(&mut acc, key(99), 2_000),
            Err(VestingError::Unauthorized),
        );
        assert_eq!(acc.claimed, 0);
    }

    #[test]
    fn claim_before_init_rejected() {
        let mut acc = VestingAccount::default();
        assert_eq!(
            apply_claim(&mut acc, key(1), 2_000),
            Err(VestingError::NotInitialized),
        );
    }
}
