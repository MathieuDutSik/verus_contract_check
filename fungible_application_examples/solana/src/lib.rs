use borsh::{BorshDeserialize, BorshSerialize};
use solana_program::{
    account_info::{next_account_info, AccountInfo},
    entrypoint,
    entrypoint::ProgramResult,
    msg,
    program_error::ProgramError,
    pubkey::Pubkey,
};

#[derive(BorshSerialize, BorshDeserialize, Debug, Default)]
pub struct Mint {
    pub total_supply: u128,
    pub initialized: bool,
}

#[derive(BorshSerialize, BorshDeserialize, Debug, Default)]
pub struct TokenAccount {
    pub owner: Pubkey,
    pub balance: u128,
}

#[derive(BorshSerialize, BorshDeserialize, Debug)]
pub enum Instruction {
    InitMint { total_supply: u128 },
    Transfer { amount: u128 },
}

entrypoint!(process_instruction);

pub fn process_instruction(
    _program_id: &Pubkey,
    accounts: &[AccountInfo],
    data: &[u8],
) -> ProgramResult {
    let instruction = Instruction::try_from_slice(data).map_err(|_| ProgramError::InvalidInstructionData)?;
    match instruction {
        Instruction::InitMint { total_supply } => init_mint(accounts, total_supply),
        Instruction::Transfer { amount } => transfer(accounts, amount),
    }
}

pub fn apply_init_mint(mint: &mut Mint, owner_acc: &mut TokenAccount, owner_key: Pubkey, total_supply: u128) -> Result<(), ProgramError> {
    if mint.initialized { return Err(ProgramError::AccountAlreadyInitialized); }
    mint.total_supply = total_supply;
    mint.initialized = true;
    owner_acc.owner = owner_key;
    owner_acc.balance = total_supply;
    Ok(())
}

pub fn apply_transfer(src: &mut TokenAccount, dst: &mut TokenAccount, signer_key: Pubkey, amount: u128) -> Result<(), ProgramError> {
    if src.owner != signer_key { return Err(ProgramError::IllegalOwner); }
    if signer_key == dst.owner { return Err(ProgramError::InvalidArgument); }
    src.balance = src.balance.checked_sub(amount).ok_or(ProgramError::InsufficientFunds)?;
    dst.balance = dst.balance.checked_add(amount).ok_or(ProgramError::ArithmeticOverflow)?;
    Ok(())
}

fn init_mint(accounts: &[AccountInfo], total_supply: u128) -> ProgramResult {
    let it = &mut accounts.iter();
    let mint_acc = next_account_info(it)?;
    let owner_acc = next_account_info(it)?;
    let mut mint = Mint::try_from_slice(&mint_acc.data.borrow())?;
    let mut owner = TokenAccount::try_from_slice(&owner_acc.data.borrow())?;
    apply_init_mint(&mut mint, &mut owner, *owner_acc.key, total_supply)?;
    mint.serialize(&mut &mut mint_acc.data.borrow_mut()[..])?;
    owner.serialize(&mut &mut owner_acc.data.borrow_mut()[..])?;
    msg!("mint initialized: supply={}", total_supply);
    Ok(())
}

fn transfer(accounts: &[AccountInfo], amount: u128) -> ProgramResult {
    let it = &mut accounts.iter();
    let signer = next_account_info(it)?;
    let src = next_account_info(it)?;
    let dst = next_account_info(it)?;
    if !signer.is_signer { return Err(ProgramError::MissingRequiredSignature); }

    let mut src_acc = TokenAccount::try_from_slice(&src.data.borrow())?;
    let mut dst_acc = TokenAccount::try_from_slice(&dst.data.borrow())?;
    apply_transfer(&mut src_acc, &mut dst_acc, *signer.key, amount)?;
    src_acc.serialize(&mut &mut src.data.borrow_mut()[..])?;
    dst_acc.serialize(&mut &mut dst.data.borrow_mut()[..])?;
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
        let mut mint = Mint::default();
        let mut owner_acc = TokenAccount::default();
        apply_init_mint(&mut mint, &mut owner_acc, owner_key, supply).unwrap();
        let alice_acc = TokenAccount { owner: alice_key, balance: 0 };
        let bob_acc   = TokenAccount { owner: bob_key,   balance: 0 };
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
        assert!(matches!(err, ProgramError::InsufficientFunds));
    }

    #[test]
    fn self_transfer_rejected() {
        let (_, mut owner_acc, _, _, owner_key, _, _) = setup(1_000);
        let mut self_acc = TokenAccount { owner: owner_key, balance: 0 };
        let err = apply_transfer(&mut owner_acc, &mut self_acc, owner_key, 10).unwrap_err();
        assert!(matches!(err, ProgramError::InvalidArgument));
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
}
