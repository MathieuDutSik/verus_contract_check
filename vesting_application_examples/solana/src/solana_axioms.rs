// Axiomatization of the Solana runtime types the vesting program
// uses. Mirrors the per-chain `*_axioms.rs` files across the other
// vesting crates.
//
// What lives here:
//   - External type specs: `Pubkey`, `AccountInfo`.
//   - `VestingError` enum + `VestingAccount` data struct. They're part
//     of the read/write axiom signatures and the verified helpers'
//     bodies, so they need to be visible to both — putting them here
//     keeps that visibility neat.
//   - Ghost spec functions: `ai_signed`, `ai_key`, `ai_vesting_data`,
//     `the_now_secs`.
//   - Axiomatized accessor wrappers around `AccountInfo` and the Clock
//     sysvar: `read_is_signer`, `read_key`, `read_vesting_data`,
//     `write_vesting_data`, `read_now_secs`.
//
// TRUST: every line below this banner enlarges the TCB. The axioms
// claim what these accessors do; we trust the Solana runtime to
// actually do them (in particular the Borsh round-trip on
// `read_vesting_data` / `write_vesting_data`).

use borsh::{BorshDeserialize, BorshSerialize};
use solana_program::{
    account_info::AccountInfo,
    pubkey::Pubkey,
    sysvar::{clock::Clock, Sysvar},
};
use vstd::prelude::*;

verus! {
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
