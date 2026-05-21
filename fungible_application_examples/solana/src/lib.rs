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

fn init_mint(accounts: &[AccountInfo], total_supply: u128) -> ProgramResult {
    let it = &mut accounts.iter();
    let mint_acc = next_account_info(it)?;
    let owner_acc = next_account_info(it)?;
    let mut mint = Mint::try_from_slice(&mint_acc.data.borrow())?;
    if mint.initialized { return Err(ProgramError::AccountAlreadyInitialized); }
    mint.total_supply = total_supply;
    mint.initialized = true;
    mint.serialize(&mut &mut mint_acc.data.borrow_mut()[..])?;

    let mut owner = TokenAccount::try_from_slice(&owner_acc.data.borrow())?;
    owner.owner = *owner_acc.key;
    owner.balance = total_supply;
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
    if src_acc.owner != *signer.key { return Err(ProgramError::IllegalOwner); }
    src_acc.balance = src_acc.balance.checked_sub(amount).ok_or(ProgramError::InsufficientFunds)?;
    dst_acc.balance = dst_acc.balance.checked_add(amount).ok_or(ProgramError::ArithmeticOverflow)?;
    src_acc.serialize(&mut &mut src.data.borrow_mut()[..])?;
    dst_acc.serialize(&mut &mut dst.data.borrow_mut()[..])?;
    Ok(())
}
