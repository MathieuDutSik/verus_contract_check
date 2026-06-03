// Axiomatization of the Solana runtime types the fungible program
// uses. Mirrors the per-chain `*_axioms.rs` files across the other
// fungible crates (cw_axioms.rs, ic_axioms.rs, gear_axioms.rs, etc.).
//
// What lives here:
//   - External type specs: `Pubkey`, `AccountInfo`.
//   - `TokenError` enum + `Mint` / `TokenAccount` data structs. They
//     participate in axiom signatures (read_*/write_*) and the verified
//     helpers' bodies, so they need to be visible to both.
//   - Ghost spec functions: `ai_signed`, `ai_key`, `ai_token_data`,
//     `ai_mint_data`.
//   - Axiomatized accessor wrappers around `AccountInfo`:
//     `read_is_signer`, `read_key`, `read_token_data`,
//     `write_token_data`, `read_mint_data`, `write_mint_data`.
//
// TRUST: every line below this banner enlarges the TCB. The axioms
// claim what these accessors do; we trust the Solana runtime to
// actually do them (in particular the Borsh round-trip on
// `read_token_data` / `write_token_data` etc.).

use borsh::{BorshDeserialize, BorshSerialize};
use solana_program::{account_info::AccountInfo, pubkey::Pubkey};
use vstd::prelude::*;

verus! {
    // External types from solana_program — opaque to Verus.
    #[verifier::external_type_specification]
    #[verifier::external_body]
    pub struct ExPubkey(#[allow(dead_code)] Pubkey);

    #[verifier::external_type_specification]
    #[verifier::external_body]
    pub struct ExAccountInfo<'a>(#[allow(dead_code)] AccountInfo<'a>);

    /// Verus-friendly error enum returned by `apply_*` helpers. The
    /// unverified entry-point glue maps these to `ProgramError`.
    #[derive(Debug, PartialEq, Eq)]
    pub enum TokenError {
        AlreadyInitialized,
        NotInitialized,
        IllegalOwner,
        InsufficientFunds,
        Overflow,
        InvalidArgument,
        MissingSignature,
        DeserializationFailed,
    }

    // Equality on Pubkey — needed because `if a == b` lowers to PartialEq::eq.
    pub assume_specification
        [ <Pubkey as ::core::cmp::PartialEq>::eq ]
        (a: &Pubkey, b: &Pubkey) -> (r: bool)
        ensures r == (*a == *b);

    // -- Ghost views of AccountInfo state -----------------------------------
    //
    // These are uninterpreted spec functions; the chain-runtime axioms
    // below describe how the `is_signer`, `key`, and account `data` map
    // to them. The Borsh round-trip is folded into `ai_token_data` /
    // `ai_mint_data` as a single ghost projection — we treat the bytes
    // ↔ struct conversion as faithful (Borsh axiom).

    pub uninterp spec fn ai_signed<'a>(a: &AccountInfo<'a>) -> bool;
    pub uninterp spec fn ai_key<'a>(a: &AccountInfo<'a>) -> Pubkey;
    pub uninterp spec fn ai_token_data<'a>(a: &AccountInfo<'a>) -> TokenAccount;
    pub uninterp spec fn ai_mint_data<'a>(a: &AccountInfo<'a>) -> Mint;

    // -- AccountInfo accessor axioms ----------------------------------------
    //
    // CHAIN-RUNTIME TRUST: these wrap the raw AccountInfo accessors with
    // Verus-aware specs. We trust the SVM to set `is_signer` truthfully,
    // to give us the right `key`, and Borsh to faithfully round-trip
    // structured data through the account buffer.

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

    // The Borsh round-trip is the trusted axiom: under normal builds
    // these wrappers call `try_from_slice` / `serialize`; under
    // `verus_only` (when Borsh derives are cfg-gated out), the bodies
    // fall back to returning Err — they're never executed because
    // Verus doesn't run programs, only verifies them.

    #[verifier::external_body]
    pub fn read_token_data<'a>(a: &AccountInfo<'a>) -> (r: Result<TokenAccount, TokenError>)
        ensures
            match r {
                Ok(td) => td == ai_token_data(a),
                Err(_) => true,
            },
    {
        #[cfg(not(verus_only))]
        return TokenAccount::try_from_slice(&a.data.borrow())
            .map_err(|_| TokenError::DeserializationFailed);
        #[cfg(verus_only)]
        Err(TokenError::DeserializationFailed)
    }

    #[verifier::external_body]
    pub fn write_token_data<'a>(a: &AccountInfo<'a>, data: &TokenAccount) -> (r: Result<(), TokenError>)
        ensures
            match r {
                Ok(()) => ai_token_data(a) == *data,
                Err(_) => true,
            },
    {
        #[cfg(not(verus_only))]
        return data.serialize(&mut &mut a.data.borrow_mut()[..])
            .map_err(|_| TokenError::DeserializationFailed);
        #[cfg(verus_only)]
        Err(TokenError::DeserializationFailed)
    }

    #[verifier::external_body]
    pub fn read_mint_data<'a>(a: &AccountInfo<'a>) -> (r: Result<Mint, TokenError>)
        ensures
            match r {
                Ok(md) => md == ai_mint_data(a),
                Err(_) => true,
            },
    {
        #[cfg(not(verus_only))]
        return Mint::try_from_slice(&a.data.borrow())
            .map_err(|_| TokenError::DeserializationFailed);
        #[cfg(verus_only)]
        Err(TokenError::DeserializationFailed)
    }

    #[verifier::external_body]
    pub fn write_mint_data<'a>(a: &AccountInfo<'a>, data: &Mint) -> (r: Result<(), TokenError>)
        ensures
            match r {
                Ok(()) => ai_mint_data(a) == *data,
                Err(_) => true,
            },
    {
        #[cfg(not(verus_only))]
        return data.serialize(&mut &mut a.data.borrow_mut()[..])
            .map_err(|_| TokenError::DeserializationFailed);
        #[cfg(verus_only)]
        Err(TokenError::DeserializationFailed)
    }

    #[cfg_attr(not(verus_only), derive(BorshSerialize, BorshDeserialize))]
    #[derive(Debug, Default)]
    pub struct Mint {
        pub total_supply: u128,
        pub initialized:  bool,
    }

    #[cfg_attr(not(verus_only), derive(BorshSerialize, BorshDeserialize))]
    #[derive(Debug, Default)]
    pub struct TokenAccount {
        pub owner:             Pubkey,
        pub balance:           u128,
        /// Address authorised to spend up to `delegated_amount` from this
        /// account. `None` means no delegation.
        pub delegate:          Option<Pubkey>,
        pub delegated_amount:  u128,
    }
}
