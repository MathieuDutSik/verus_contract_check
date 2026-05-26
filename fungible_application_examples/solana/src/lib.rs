// Solana fungible-token program with Verus-verified arithmetic + allowance
// logic.
//
// Solana's data model: state lives in account data buffers, not in
// per-instance struct state. Each instruction takes a `&[AccountInfo]`
// in positional order; the program serialises/deserialises the buffers
// via Borsh. Authorization is via `signer.is_signer` flags on the
// `AccountInfo`s.
//
// We factor the work into:
//   - Layer 1 (`core.rs`): chain-agnostic State<A> + conservation lemmas.
//   - Layer 2 (`apply_*` functions in this file, inside `verus!{}`):
//     pure-data updates on `Mint` / `TokenAccount` with `ensures`
//     proving the safety properties (balance conservation, signer/owner
//     check, allowance decrement).
//   - Layer 3 (entry-point `process_instruction`): unverified glue —
//     deserialises account data, calls the verified apply_*, reserialises.
//
// We extend the existing `TokenAccount` with cw20/SPL-Token style
// allowance fields (`delegate`, `delegated_amount`) so we can verify
// approve / transfer_from / revoke.

pub mod core;

use borsh::{BorshDeserialize, BorshSerialize};
use solana_program::{
    account_info::{next_account_info, AccountInfo},
    entrypoint,
    entrypoint::ProgramResult,
    msg,
    program_error::ProgramError,
    pubkey::Pubkey,
};

// Struct definitions inside verus!{} so Verus sees them natively. Borsh
// derives work in this context (they produce plain Rust which Verus
// passes through).
vstd::prelude::verus! {
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

#[cfg_attr(not(verus_only), derive(BorshSerialize, BorshDeserialize))]
#[derive(Debug)]
pub enum Instruction {
    InitMint     { total_supply: u128 },
    Transfer     { amount: u128 },
    Approve      { amount: u128 },
    Revoke,
    TransferFrom { amount: u128 },
    Mint         { amount: u128 },
    Burn         { amount: u128 },
}

#[cfg(not(verus_only))]
entrypoint!(process_instruction);

#[cfg(not(verus_only))]
pub fn process_instruction(
    _program_id: &Pubkey,
    accounts: &[AccountInfo],
    data: &[u8],
) -> ProgramResult {
    let instruction = Instruction::try_from_slice(data).map_err(|_| ProgramError::InvalidInstructionData)?;
    match instruction {
        Instruction::InitMint     { total_supply } => init_mint(accounts, total_supply),
        Instruction::Transfer     { amount }       => transfer(accounts, amount),
        Instruction::Approve      { amount }       => approve(accounts, amount),
        Instruction::Revoke                        => revoke(accounts),
        Instruction::TransferFrom { amount }       => transfer_from(accounts, amount),
        Instruction::Mint         { amount }       => mint(accounts, amount),
        Instruction::Burn         { amount }       => burn(accounts, amount),
    }
}

// -- Verified apply_* helpers ------------------------------------------
//
// Each takes owned mutable references to the relevant data structures
// and a signer's pubkey. The `ensures` clauses pin down the
// safety-relevant effects: balance conservation, signer/owner checks,
// allowance decrements.

vstd::prelude::verus! {
    #[cfg(verus_only)]
    use vstd::prelude::*;

    /// Initialise the mint and credit the entire supply to the owner.
    pub fn apply_init_mint(
        mint:      &mut Mint,
        owner_acc: &mut TokenAccount,
        owner_key: Pubkey,
        total_supply: u128,
    ) -> (r: Result<(), TokenError>)
        ensures
            match r {
                Ok(()) =>
                    !old(mint).initialized
                    && final(mint).initialized
                    && final(mint).total_supply == total_supply
                    && final(owner_acc).owner == owner_key
                    && final(owner_acc).balance == total_supply,
                Err(_) => true,
            },
    {
        if mint.initialized { return Err(TokenError::AlreadyInitialized); }
        mint.total_supply = total_supply;
        mint.initialized = true;
        owner_acc.owner = owner_key;
        owner_acc.balance = total_supply;
        Ok(())
    }

    /// Transfer `amount` from `src` to `dst`, signed by `signer_key`.
    /// Requires `signer_key == src.owner` and `signer_key != dst.owner`.
    pub fn apply_transfer(
        src:        &mut TokenAccount,
        dst:        &mut TokenAccount,
        signer_key: Pubkey,
        amount:     u128,
    ) -> (r: Result<(), TokenError>)
        ensures
            match r {
                Ok(()) =>
                    old(src).owner == signer_key
                    && signer_key != old(dst).owner
                    && final(src).balance + final(dst).balance
                        == old(src).balance + old(dst).balance
                    && final(src).balance == (old(src).balance - amount) as u128
                    && final(dst).balance == (old(dst).balance + amount) as u128,
                Err(_) => true,
            },
    {
        if src.owner != signer_key { return Err(TokenError::IllegalOwner); }
        if signer_key == dst.owner { return Err(TokenError::InvalidArgument); }
        let src_next = match src.balance.checked_sub(amount) {
            Some(v) => v,
            None    => return Err(TokenError::InsufficientFunds),
        };
        let dst_next = match dst.balance.checked_add(amount) {
            Some(v) => v,
            None    => return Err(TokenError::Overflow),
        };
        src.balance = src_next;
        dst.balance = dst_next;
        Ok(())
    }

    // -- End-to-end verified transfer instruction -----------------------
    //
    // Combines: positional account parsing + signer check + owner check
    // + balance arithmetic + writeback. The `ensures` describes the
    // entire effect of running the Transfer instruction.
    pub fn verified_transfer_instruction<'a>(
        accounts: &'a [AccountInfo<'a>],
        amount:   u128,
    ) -> (r: Result<(), TokenError>)
        ensures
            match r {
                Ok(()) =>
                    accounts.len() >= 3
                    && ai_signed(&accounts[0]),
                // We deliberately keep this `ensures` minimal: it only
                // claims the parser-level guarantees that are framing-free
                // (the signer flag and account-list length).
                //
                // The substantive properties — `apply_transfer`'s conservation,
                // signer's pubkey matching `src.owner`, distinctness of
                // src vs dst — are proven inside the called helpers'
                // own ensures. The `ai_token_data` spec function is
                // *uninterpreted* (returns "the current view") and
                // Verus's pure-function model means we can't easily
                // pre/post-state it across a writeback without an
                // explicit state-tracking layer.
                //
                // What this ensures *does* establish for the caller:
                // any code path leading to `Ok(())` has passed the
                // length check AND the is_signer check — i.e., the two
                // bug classes ("forgot to check arg count", "forgot to
                // check signer") cannot exist in this function.
                Err(_) => true,
            },
    {
        // 1. Positional + length check.
        if accounts.len() < 3 {
            return Err(TokenError::InvalidArgument);
        }
        let signer = &accounts[0];
        let src    = &accounts[1];
        let dst    = &accounts[2];

        // 2. Signer check.
        if !read_is_signer(signer) {
            return Err(TokenError::MissingSignature);
        }

        // 3. Read account data.
        let mut src_data = match read_token_data(src) {
            Ok(d)  => d,
            Err(e) => return Err(e),
        };
        let mut dst_data = match read_token_data(dst) {
            Ok(d)  => d,
            Err(e) => return Err(e),
        };

        // 4. Owner / distinctness checks (folded into apply_transfer's
        //    own checks, but we want them visible at the dispatch layer).
        let signer_key = read_key(signer);

        // 5. Verified arithmetic + state update.
        apply_transfer(&mut src_data, &mut dst_data, signer_key, amount)?;

        // 6. Writeback to the same AccountInfos we just read from.
        write_token_data(src, &src_data)?;
        write_token_data(dst, &dst_data)?;

        Ok(())
    }

    /// Approve `delegate_key` to spend up to `amount` from `src`. The
    /// caller must be `src.owner`. Overwrites any previous delegation.
    pub fn apply_approve(
        src:          &mut TokenAccount,
        signer_key:   Pubkey,
        delegate_key: Pubkey,
        amount:       u128,
    ) -> (r: Result<(), TokenError>)
        ensures
            match r {
                Ok(()) =>
                    old(src).owner == signer_key
                    && final(src).delegate == Some(delegate_key)
                    && final(src).delegated_amount == amount
                    && final(src).balance == old(src).balance
                    && final(src).owner == old(src).owner,
                Err(_) => true,
            },
    {
        if src.owner != signer_key { return Err(TokenError::IllegalOwner); }
        src.delegate = Some(delegate_key);
        src.delegated_amount = amount;
        Ok(())
    }

    /// Revoke the current delegation on `src`. Caller must be `src.owner`.
    pub fn apply_revoke(
        src:        &mut TokenAccount,
        signer_key: Pubkey,
    ) -> (r: Result<(), TokenError>)
        ensures
            match r {
                Ok(()) =>
                    old(src).owner == signer_key
                    && final(src).delegate is None
                    && final(src).delegated_amount == 0u128
                    && final(src).balance == old(src).balance,
                Err(_) => true,
            },
    {
        if src.owner != signer_key { return Err(TokenError::IllegalOwner); }
        src.delegate = None;
        src.delegated_amount = 0;
        Ok(())
    }

    /// Transfer `amount` from `src` to `dst`, signed by `spender_key`
    /// which must equal `src.delegate` and have at least `amount`
    /// remaining in `delegated_amount`. The delegation is decremented
    /// by `amount`.
    pub fn apply_transfer_from(
        src:         &mut TokenAccount,
        dst:         &mut TokenAccount,
        spender_key: Pubkey,
        amount:      u128,
    ) -> (r: Result<(), TokenError>)
        ensures
            match r {
                Ok(()) =>
                    old(src).delegate == Some(spender_key)
                    && old(src).delegated_amount >= amount
                    && spender_key != old(dst).owner
                    && final(src).balance + final(dst).balance
                        == old(src).balance + old(dst).balance
                    && final(src).balance == (old(src).balance - amount) as u128
                    && final(dst).balance == (old(dst).balance + amount) as u128
                    && final(src).delegated_amount == (old(src).delegated_amount - amount) as u128
                    && final(src).delegate == old(src).delegate
                    && final(src).owner == old(src).owner,
                Err(_) => true,
            },
    {
        // Authorization: spender must equal the delegate.
        match src.delegate {
            Some(d) if d == spender_key => {}
            _ => return Err(TokenError::IllegalOwner),
        }
        if src.delegated_amount < amount {
            return Err(TokenError::InsufficientFunds);
        }
        if spender_key == dst.owner { return Err(TokenError::InvalidArgument); }
        let src_next = match src.balance.checked_sub(amount) {
            Some(v) => v,
            None    => return Err(TokenError::InsufficientFunds),
        };
        let dst_next = match dst.balance.checked_add(amount) {
            Some(v) => v,
            None    => return Err(TokenError::Overflow),
        };
        src.balance = src_next;
        dst.balance = dst_next;
        src.delegated_amount = src.delegated_amount - amount;
        Ok(())
    }

    /// Mint `amount` to `dst`, increasing total supply by the same.
    /// Caller must be the mint authority (modelled as the signer who
    /// initialised the mint — here, simply allowed by signature).
    pub fn apply_mint(
        mint:   &mut Mint,
        dst:    &mut TokenAccount,
        amount: u128,
    ) -> (r: Result<(), TokenError>)
        ensures
            match r {
                Ok(()) =>
                    old(mint).initialized
                    && final(mint).total_supply == (old(mint).total_supply + amount) as u128
                    && final(dst).balance == (old(dst).balance + amount) as u128
                    && final(mint).initialized == old(mint).initialized,
                Err(_) => true,
            },
    {
        if !mint.initialized { return Err(TokenError::NotInitialized); }
        let new_supply = match mint.total_supply.checked_add(amount) {
            Some(v) => v,
            None    => return Err(TokenError::Overflow),
        };
        let new_bal = match dst.balance.checked_add(amount) {
            Some(v) => v,
            None    => return Err(TokenError::Overflow),
        };
        mint.total_supply = new_supply;
        dst.balance = new_bal;
        Ok(())
    }

    /// Burn `amount` from `src`, decreasing total supply by the same.
    /// Caller must be `src.owner`.
    pub fn apply_burn(
        mint:       &mut Mint,
        src:        &mut TokenAccount,
        signer_key: Pubkey,
        amount:     u128,
    ) -> (r: Result<(), TokenError>)
        ensures
            match r {
                Ok(()) =>
                    old(src).owner == signer_key
                    && final(mint).total_supply == (old(mint).total_supply - amount) as u128
                    && final(src).balance == (old(src).balance - amount) as u128,
                Err(_) => true,
            },
    {
        if src.owner != signer_key { return Err(TokenError::IllegalOwner); }
        let new_bal = match src.balance.checked_sub(amount) {
            Some(v) => v,
            None    => return Err(TokenError::InsufficientFunds),
        };
        let new_supply = match mint.total_supply.checked_sub(amount) {
            Some(v) => v,
            None    => return Err(TokenError::InsufficientFunds),
        };
        src.balance = new_bal;
        mint.total_supply = new_supply;
        Ok(())
    }
}

// -- Unverified entry-point glue ---------------------------------------
// Each fn deserialises the relevant accounts, calls the verified
// apply_* helper, then writes back. The deserialise/serialise dance and
// the AccountInfo positional ordering remain unverified.
//
// All of this is cfg-gated out during verification (verus_only set)
// because Borsh's std::io::Error and Solana's AccountInfo aren't
// Verus-known types.

#[cfg(not(verus_only))]
fn token_err_to_program_err(e: TokenError) -> ProgramError {
    match e {
        TokenError::AlreadyInitialized    => ProgramError::AccountAlreadyInitialized,
        TokenError::NotInitialized        => ProgramError::UninitializedAccount,
        TokenError::IllegalOwner          => ProgramError::IllegalOwner,
        TokenError::InsufficientFunds     => ProgramError::InsufficientFunds,
        TokenError::Overflow              => ProgramError::ArithmeticOverflow,
        TokenError::InvalidArgument       => ProgramError::InvalidArgument,
        TokenError::MissingSignature      => ProgramError::MissingRequiredSignature,
        TokenError::DeserializationFailed => ProgramError::InvalidAccountData,
    }
}

#[cfg(not(verus_only))]
fn init_mint(accounts: &[AccountInfo], total_supply: u128) -> ProgramResult {
    let it = &mut accounts.iter();
    let mint_acc  = next_account_info(it)?;
    let owner_acc = next_account_info(it)?;
    let mut mint  = Mint::try_from_slice(&mint_acc.data.borrow())?;
    let mut owner = TokenAccount::try_from_slice(&owner_acc.data.borrow())?;
    apply_init_mint(&mut mint, &mut owner, *owner_acc.key, total_supply).map_err(token_err_to_program_err)?;
    mint.serialize(&mut &mut mint_acc.data.borrow_mut()[..])?;
    owner.serialize(&mut &mut owner_acc.data.borrow_mut()[..])?;
    msg!("mint initialized: supply={}", total_supply);
    Ok(())
}

#[cfg(not(verus_only))]
fn transfer(accounts: &[AccountInfo], amount: u128) -> ProgramResult {
    let it = &mut accounts.iter();
    let signer = next_account_info(it)?;
    let src    = next_account_info(it)?;
    let dst    = next_account_info(it)?;
    if !signer.is_signer { return Err(ProgramError::MissingRequiredSignature); }
    let mut src_acc = TokenAccount::try_from_slice(&src.data.borrow())?;
    let mut dst_acc = TokenAccount::try_from_slice(&dst.data.borrow())?;
    apply_transfer(&mut src_acc, &mut dst_acc, *signer.key, amount).map_err(token_err_to_program_err)?;
    src_acc.serialize(&mut &mut src.data.borrow_mut()[..])?;
    dst_acc.serialize(&mut &mut dst.data.borrow_mut()[..])?;
    Ok(())
}

#[cfg(not(verus_only))]
fn approve(accounts: &[AccountInfo], amount: u128) -> ProgramResult {
    let it = &mut accounts.iter();
    let signer       = next_account_info(it)?;
    let src          = next_account_info(it)?;
    let delegate_acc = next_account_info(it)?;
    if !signer.is_signer { return Err(ProgramError::MissingRequiredSignature); }
    let mut src_acc = TokenAccount::try_from_slice(&src.data.borrow())?;
    apply_approve(&mut src_acc, *signer.key, *delegate_acc.key, amount).map_err(token_err_to_program_err)?;
    src_acc.serialize(&mut &mut src.data.borrow_mut()[..])?;
    Ok(())
}

#[cfg(not(verus_only))]
fn revoke(accounts: &[AccountInfo]) -> ProgramResult {
    let it = &mut accounts.iter();
    let signer = next_account_info(it)?;
    let src    = next_account_info(it)?;
    if !signer.is_signer { return Err(ProgramError::MissingRequiredSignature); }
    let mut src_acc = TokenAccount::try_from_slice(&src.data.borrow())?;
    apply_revoke(&mut src_acc, *signer.key).map_err(token_err_to_program_err)?;
    src_acc.serialize(&mut &mut src.data.borrow_mut()[..])?;
    Ok(())
}

#[cfg(not(verus_only))]
fn transfer_from(accounts: &[AccountInfo], amount: u128) -> ProgramResult {
    let it = &mut accounts.iter();
    let spender = next_account_info(it)?;
    let src     = next_account_info(it)?;
    let dst     = next_account_info(it)?;
    if !spender.is_signer { return Err(ProgramError::MissingRequiredSignature); }
    let mut src_acc = TokenAccount::try_from_slice(&src.data.borrow())?;
    let mut dst_acc = TokenAccount::try_from_slice(&dst.data.borrow())?;
    apply_transfer_from(&mut src_acc, &mut dst_acc, *spender.key, amount).map_err(token_err_to_program_err)?;
    src_acc.serialize(&mut &mut src.data.borrow_mut()[..])?;
    dst_acc.serialize(&mut &mut dst.data.borrow_mut()[..])?;
    Ok(())
}

#[cfg(not(verus_only))]
fn mint(accounts: &[AccountInfo], amount: u128) -> ProgramResult {
    let it = &mut accounts.iter();
    let _authority = next_account_info(it)?;
    let mint_acc   = next_account_info(it)?;
    let dst        = next_account_info(it)?;
    if !_authority.is_signer { return Err(ProgramError::MissingRequiredSignature); }
    let mut mint_data = Mint::try_from_slice(&mint_acc.data.borrow())?;
    let mut dst_acc   = TokenAccount::try_from_slice(&dst.data.borrow())?;
    apply_mint(&mut mint_data, &mut dst_acc, amount).map_err(token_err_to_program_err)?;
    mint_data.serialize(&mut &mut mint_acc.data.borrow_mut()[..])?;
    dst_acc.serialize(&mut &mut dst.data.borrow_mut()[..])?;
    Ok(())
}

#[cfg(not(verus_only))]
fn burn(accounts: &[AccountInfo], amount: u128) -> ProgramResult {
    let it = &mut accounts.iter();
    let signer   = next_account_info(it)?;
    let mint_acc = next_account_info(it)?;
    let src      = next_account_info(it)?;
    if !signer.is_signer { return Err(ProgramError::MissingRequiredSignature); }
    let mut mint_data = Mint::try_from_slice(&mint_acc.data.borrow())?;
    let mut src_acc   = TokenAccount::try_from_slice(&src.data.borrow())?;
    apply_burn(&mut mint_data, &mut src_acc, *signer.key, amount).map_err(token_err_to_program_err)?;
    mint_data.serialize(&mut &mut mint_acc.data.borrow_mut()[..])?;
    src_acc.serialize(&mut &mut src.data.borrow_mut()[..])?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn pk(b: u8) -> Pubkey { Pubkey::new_from_array([b; 32]) }

    fn setup(supply: u128) -> (Mint, TokenAccount, TokenAccount, TokenAccount, Pubkey, Pubkey, Pubkey) {
        let owner_key = pk(1);
        let alice_key = pk(2);
        let bob_key   = pk(3);
        let mut mint  = Mint::default();
        let mut owner_acc = TokenAccount::default();
        apply_init_mint(&mut mint, &mut owner_acc, owner_key, supply).unwrap();
        let alice_acc = TokenAccount { owner: alice_key, balance: 0, delegate: None, delegated_amount: 0 };
        let bob_acc   = TokenAccount { owner: bob_key,   balance: 0, delegate: None, delegated_amount: 0 };
        (mint, owner_acc, alice_acc, bob_acc, owner_key, alice_key, bob_key)
    }

    #[test]
    fn init_supply_credited_to_owner() {
        let (mint, owner_acc, _, _, owner_key, _, _) = setup(1_000);
        assert_eq!(mint.total_supply, 1_000);
        assert!(mint.initialized);
        assert_eq!(owner_acc.balance, 1_000);
        assert_eq!(owner_acc.owner, owner_key);
    }

    #[test]
    fn balance_of_unknown_is_zero() {
        let fresh = TokenAccount::default();
        assert_eq!(fresh.balance, 0);
    }

    #[test]
    fn transfer_happy_path() {
        let (_, mut owner_acc, mut alice_acc, _, owner_key, _, _) = setup(1_000);
        apply_transfer(&mut owner_acc, &mut alice_acc, owner_key, 250).unwrap();
        assert_eq!(owner_acc.balance, 750);
        assert_eq!(alice_acc.balance, 250);
    }

    #[test]
    fn transfer_insufficient_balance() {
        let (_, mut owner_acc, mut alice_acc, _, owner_key, _, _) = setup(100);
        let err = apply_transfer(&mut owner_acc, &mut alice_acc, owner_key, 200).unwrap_err();
        assert!(matches!(err, TokenError::InsufficientFunds));
    }

    #[test]
    fn self_transfer_rejected() {
        let (_, mut owner_acc, _, _, owner_key, _, _) = setup(1_000);
        let mut self_acc = TokenAccount { owner: owner_key, balance: 0, delegate: None, delegated_amount: 0 };
        let err = apply_transfer(&mut owner_acc, &mut self_acc, owner_key, 10).unwrap_err();
        assert!(matches!(err, TokenError::InvalidArgument));
    }

    #[test]
    fn total_supply_invariant_after_transfer() {
        let (mint, mut owner_acc, mut alice_acc, bob_acc, owner_key, _, _) = setup(1_000);
        for amt in [100u128, 200, 50] {
            apply_transfer(&mut owner_acc, &mut alice_acc, owner_key, amt).unwrap();
        }
        let sum = owner_acc.balance + alice_acc.balance + bob_acc.balance;
        assert_eq!(sum, mint.total_supply);
    }

    // -- Allowance tests --------------------------------------------------

    #[test]
    fn approve_sets_delegate() {
        let (_, mut owner_acc, _, _, owner_key, alice_key, _) = setup(1_000);
        apply_approve(&mut owner_acc, owner_key, alice_key, 250).unwrap();
        assert_eq!(owner_acc.delegate, Some(alice_key));
        assert_eq!(owner_acc.delegated_amount, 250);
    }

    #[test]
    fn approve_by_non_owner_rejected() {
        let (_, mut owner_acc, _, _, _, alice_key, bob_key) = setup(1_000);
        let err = apply_approve(&mut owner_acc, alice_key, bob_key, 250).unwrap_err();
        assert!(matches!(err, TokenError::IllegalOwner));
    }

    #[test]
    fn transfer_from_happy_path() {
        let (_, mut owner_acc, _, mut bob_acc, owner_key, alice_key, _) = setup(1_000);
        apply_approve(&mut owner_acc, owner_key, alice_key, 250).unwrap();
        apply_transfer_from(&mut owner_acc, &mut bob_acc, alice_key, 200).unwrap();
        assert_eq!(owner_acc.balance, 800);
        assert_eq!(bob_acc.balance, 200);
        assert_eq!(owner_acc.delegated_amount, 50);
    }

    #[test]
    fn transfer_from_insufficient_allowance() {
        let (_, mut owner_acc, _, mut bob_acc, owner_key, alice_key, _) = setup(1_000);
        apply_approve(&mut owner_acc, owner_key, alice_key, 100).unwrap();
        let err = apply_transfer_from(&mut owner_acc, &mut bob_acc, alice_key, 200).unwrap_err();
        assert!(matches!(err, TokenError::InsufficientFunds));
        // Allowance unchanged.
        assert_eq!(owner_acc.delegated_amount, 100);
    }

    #[test]
    fn transfer_from_wrong_spender() {
        let (_, mut owner_acc, _, mut bob_acc, owner_key, alice_key, _) = setup(1_000);
        apply_approve(&mut owner_acc, owner_key, alice_key, 250).unwrap();
        // Bob (not delegate) tries to spend.
        let err = apply_transfer_from(&mut owner_acc, &mut bob_acc, pk(99), 100).unwrap_err();
        assert!(matches!(err, TokenError::IllegalOwner));
    }

    #[test]
    fn revoke_clears_delegation() {
        let (_, mut owner_acc, _, _, owner_key, alice_key, _) = setup(1_000);
        apply_approve(&mut owner_acc, owner_key, alice_key, 250).unwrap();
        apply_revoke(&mut owner_acc, owner_key).unwrap();
        assert_eq!(owner_acc.delegate, None);
        assert_eq!(owner_acc.delegated_amount, 0);
    }

    // -- Mint / Burn tests ------------------------------------------------

    #[test]
    fn mint_increases_supply_and_balance() {
        let (mut mint, mut owner_acc, mut alice_acc, _, _, _, _) = setup(1_000);
        apply_mint(&mut mint, &mut alice_acc, 250).unwrap();
        assert_eq!(mint.total_supply, 1_250);
        assert_eq!(alice_acc.balance, 250);
        assert_eq!(owner_acc.balance, 1_000); // untouched
    }

    #[test]
    fn burn_decreases_supply_and_balance() {
        let (mut mint, mut owner_acc, _, _, owner_key, _, _) = setup(1_000);
        apply_burn(&mut mint, &mut owner_acc, owner_key, 250).unwrap();
        assert_eq!(mint.total_supply, 750);
        assert_eq!(owner_acc.balance, 750);
    }

    #[test]
    fn burn_by_non_owner_rejected() {
        let (mut mint, mut owner_acc, _, _, _, alice_key, _) = setup(1_000);
        let err = apply_burn(&mut mint, &mut owner_acc, alice_key, 100).unwrap_err();
        assert!(matches!(err, TokenError::IllegalOwner));
    }
}
