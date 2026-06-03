// Solana fungible-token program with Verus-verified arithmetic +
// allowance logic.
//
// Solana's data model: state lives in account data buffers, not in
// per-instance struct state. Each instruction takes a `&[AccountInfo]`
// in positional order; the program serialises/deserialises the buffers
// via Borsh. Authorization is via `signer.is_signer` flags on the
// `AccountInfo`s.
//
// Layout (mirrors `linera_alternate` fungible):
//   - `pub mod core;`              — chain-agnostic State<A> +
//                                    conservation lemmas.
//   - `pub mod solana_axioms;`     — Solana runtime axioms: Pubkey /
//                                    AccountInfo external types,
//                                    `read_*` / `write_*` accessor
//                                    wrappers, `TokenError` enum and
//                                    `Mint` / `TokenAccount` data
//                                    structs (which appear in axiom
//                                    signatures).
//   - `pub mod verified_helpers;`  — pure-data `apply_*` updates plus
//                                    `verified_transfer_instruction`
//                                    end-to-end dispatcher.
//   - this file                    — `Instruction` enum + entrypoint
//                                    + `process_instruction` glue +
//                                    per-instruction wrappers + tests.

pub mod core;
pub mod solana_axioms;
pub mod verified_helpers;

#[cfg(not(verus_only))]
use borsh::{BorshDeserialize, BorshSerialize};
#[cfg(not(verus_only))]
use solana_program::{
    account_info::{next_account_info, AccountInfo},
    entrypoint,
    entrypoint::ProgramResult,
    msg,
    program_error::ProgramError,
    pubkey::Pubkey,
};

pub use solana_axioms::{Mint, TokenAccount, TokenError};
pub use verified_helpers::{
    apply_approve, apply_burn, apply_init_mint, apply_mint, apply_revoke,
    apply_transfer, apply_transfer_from, verified_transfer_instruction,
};


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
pub fn process_instruction<'a>(
    _program_id: &Pubkey,
    accounts: &'a [AccountInfo<'a>],
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
fn transfer<'a>(accounts: &'a [AccountInfo<'a>], amount: u128) -> ProgramResult {
    // Routes through the verified instruction. The verified body covers
    // the positional + length check (`accounts.len() >= 3`), the signer
    // check (`read_is_signer(accounts[0])`), the Borsh round-trip on
    // accounts[1] / accounts[2], and the substantive `apply_transfer`
    // arithmetic + writeback. Each of those guarantees holds at the
    // dispatch level — the two most common Solana bug classes (missing
    // signer, off-by-one arg count) are structurally impossible here.
    //
    // The explicit `<'a>` is required because `AccountInfo<'a>` is
    // invariant over `'a` and `verified_transfer_instruction` declares
    // `&'a [AccountInfo<'a>]`; the bare `&[AccountInfo]` would leave the
    // outer and inner lifetimes unrelated.
    verified_transfer_instruction(accounts, amount).map_err(token_err_to_program_err)
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
