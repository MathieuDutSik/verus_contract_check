// Solana vesting program with Verus-verified arithmetic + claim
// authorisation.
//
// Solana's data model: state lives in account-data buffers, not in
// per-instance struct state. The vesting account holds the full
// `VestingAccount` record (beneficiary, schedule, claimed). The
// program serialises/deserialises the buffer via Borsh, and treats the
// `is_signer` flag on `AccountInfo` as the authorisation source.
//
// Layout (mirrors `linera_alternate` fungible):
//   - `pub mod core;`              — chain-agnostic State<A> +
//                                    schedule lemmas.
//   - `pub mod solana_axioms;`     — Solana runtime axioms: Pubkey /
//                                    AccountInfo external types,
//                                    `read_is_signer` / `read_key` /
//                                    `read_vesting_data` /
//                                    `write_vesting_data` /
//                                    `read_now_secs` wrappers, plus
//                                    the `VestingAccount` record and
//                                    `VestingError` enum (which appear
//                                    in axiom signatures).
//   - `pub mod verified_helpers;`  — `apply_init_vesting` /
//                                    `apply_claim` (pure-data updates)
//                                    plus end-to-end
//                                    `verified_init_instruction` /
//                                    `verified_claim_instruction`
//                                    dispatchers.
//   - this file                    — `Instruction` enum + entrypoint
//                                    + `process_instruction` glue +
//                                    tests.
//
// Time. The chain time is `Clock::unix_timestamp: i64` (seconds since
// the unix epoch). We axiomatise it via `the_now_secs()` ghost that
// returns a `u64` (the i64-as-u64 cast of unix_timestamp, clamped to
// 0 for pre-epoch times). The schedule downstream is in seconds.

pub mod core;
pub mod solana_axioms;
pub mod verified_helpers;

#[cfg(not(verus_only))]
use borsh::{BorshDeserialize, BorshSerialize};
#[cfg(not(verus_only))]
use solana_program::{
    account_info::AccountInfo,
    entrypoint,
    entrypoint::ProgramResult,
    program_error::ProgramError,
    pubkey::Pubkey,
};

pub use solana_axioms::{VestingAccount, VestingError};
pub use verified_helpers::{
    apply_claim, apply_init_vesting, verified_claim_instruction,
    verified_init_instruction,
};

// =====================================================================
// Solana program glue (unverified): instruction enum, entrypoint,
// dispatch, error mapping.
// =====================================================================

#[cfg_attr(not(verus_only), derive(BorshSerialize, BorshDeserialize))]
#[derive(Debug)]
pub enum Instruction {
    Init {
        beneficiary:         solana_program::pubkey::Pubkey,
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
// Tests — exercise the `apply_*` helpers directly. The instruction-
// level glue (AccountInfo, Borsh, Clock) requires either solana-test or
// a real account harness, which we don't pull in.
// =====================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use solana_program::pubkey::Pubkey;

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
