// ink! fungible-token contract with Verus-verified mint/burn arithmetic.
//
// Layout (mirrors `linera_alternate` fungible):
//   - `pub mod core;`              — chain-agnostic verified core.
//   - `pub mod verified_helpers;`  — `verified_mint_step` /
//                                    `verified_burn_step` +
//                                    `TransferError` re-export.
//   - this file                    — the `#[ink::contract]` module
//                                    with storage + messages + tests.

#![cfg_attr(not(feature = "std"), no_std, no_main)]

pub mod core;
pub mod verified_helpers;

pub use verified_helpers::{verified_burn_step, verified_mint_step};
pub use verus_fungible_core::TransferError;

// The `#[ink::contract]` macro expands to wasm dispatch + ABI code that
// depends on `Error: scale::Encode` / `scale::Decode`. Cfg-gating
// either the macro module or the derives alone breaks compilation in
// the other branch (the macro needs the impls; Verus warns on the
// derives). The fix: gate the *whole module* behind `not(verus_only)`,
// so Verus never sees the macro expansion (and therefore never sees
// the derives that it can't handle). The verified helpers
// (`verified_mint_step` / `verified_burn_step`) live outside this
// module in `verified_helpers.rs`, so verification is unaffected.
#[cfg(not(verus_only))]
#[ink::contract]
mod fungible {
    use crate::core as fcore;
    use crate::{verified_mint_step, verified_burn_step, TransferError as TE};
    use ink::storage::Mapping;

    #[ink(storage)]
    pub struct Fungible {
        total_supply: Balance,
        balances: Mapping<AccountId, Balance>,
    }

    #[derive(Debug, PartialEq, Eq, scale::Encode, scale::Decode)]
    #[cfg_attr(feature = "std", derive(scale_info::TypeInfo))]
    pub enum Error {
        InsufficientBalance,
        Overflow,
        SelfTransfer,
        InsufficientSupply,
    }

    fn map_err(e: TE) -> Error {
        match e {
            TE::SelfTransfer          => Error::SelfTransfer,
            TE::Insufficient          => Error::InsufficientBalance,
            TE::Overflow              => Error::Overflow,
            TE::InsufficientSupply    => Error::InsufficientSupply,
            TE::InsufficientAllowance => Error::Overflow, // unused on ink!
            TE::Unauthorized          => Error::Overflow, // unused on ink!
        }
    }

    #[ink(event)]
    pub struct Transfer {
        #[ink(topic)] from: AccountId,
        #[ink(topic)] to: AccountId,
        value: Balance,
    }

    impl Fungible {
        #[ink(constructor)]
        pub fn new(total_supply: Balance) -> Self {
            let caller = Self::env().caller();
            let mut balances = Mapping::default();
            balances.insert(caller, &total_supply);
            Self { total_supply, balances }
        }

        #[ink(message)]
        pub fn total_supply(&self) -> Balance { self.total_supply }

        #[ink(message)]
        pub fn balance_of(&self, account: AccountId) -> Balance {
            self.balances.get(account).unwrap_or(0)
        }

        #[ink(message)]
        pub fn transfer(&mut self, to: AccountId, value: Balance) -> Result<(), Error> {
            let from = self.env().caller();
            if from == to { return Err(Error::SelfTransfer); }
            let from_balance = self.balances.get(from).unwrap_or(0);
            let to_balance   = self.balances.get(to).unwrap_or(0);
            // Delegate the arithmetic to the Verus-verified core.
            let (from_next, to_next) = fcore::transfer_balances(from_balance, to_balance, value)
                .map_err(|msg| match msg {
                    "insufficient balance" => Error::InsufficientBalance,
                    _                      => Error::Overflow,
                })?;
            self.balances.insert(from, &from_next);
            self.balances.insert(to, &to_next);
            self.env().emit_event(Transfer { from, to, value });
            Ok(())
        }

        /// Mint `amount` tokens to `to`. No authorization check (would be
        /// added in a real cw20-like contract by storing a Minter address).
        #[ink(message)]
        pub fn mint(&mut self, to: AccountId, amount: Balance) -> Result<(), Error> {
            let to_balance = self.balances.get(to).unwrap_or(0);
            // Delegate the verified arithmetic (supply + balance both update).
            let (new_balance, new_supply) =
                verified_mint_step(to_balance, self.total_supply, amount).map_err(map_err)?;
            self.total_supply = new_supply;
            self.balances.insert(to, &new_balance);
            Ok(())
        }

        /// Burn `amount` from the caller's balance.
        #[ink(message)]
        pub fn burn(&mut self, amount: Balance) -> Result<(), Error> {
            let from = self.env().caller();
            let from_balance = self.balances.get(from).unwrap_or(0);
            let (new_balance, new_supply) =
                verified_burn_step(from_balance, self.total_supply, amount).map_err(map_err)?;
            self.total_supply = new_supply;
            self.balances.insert(from, &new_balance);
            Ok(())
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

        fn setup(supply: Balance) -> (Fungible, test::DefaultAccounts<ink::env::DefaultEnvironment>) {
            let a = accounts();
            set_caller(a.alice);
            let f = Fungible::new(supply);
            (f, a)
        }

        #[ink::test]
        fn init_supply_credited_to_owner() {
            let (f, a) = setup(1_000);
            assert_eq!(f.total_supply(), 1_000);
            assert_eq!(f.balance_of(a.alice), 1_000);
        }

        #[ink::test]
        fn balance_of_unknown_is_zero() {
            let (f, a) = setup(1_000);
            assert_eq!(f.balance_of(a.charlie), 0);
        }

        #[ink::test]
        fn transfer_happy_path() {
            let (mut f, a) = setup(1_000);
            f.transfer(a.bob, 250).unwrap();
            assert_eq!(f.balance_of(a.alice), 750);
            assert_eq!(f.balance_of(a.bob),   250);
        }

        #[ink::test]
        fn transfer_insufficient_balance() {
            let (mut f, a) = setup(100);
            assert_eq!(f.transfer(a.bob, 200), Err(Error::InsufficientBalance));
        }

        #[ink::test]
        fn self_transfer_rejected() {
            let (mut f, a) = setup(1_000);
            assert_eq!(f.transfer(a.alice, 10), Err(Error::SelfTransfer));
        }

        #[ink::test]
        fn total_supply_invariant_after_transfer() {
            let (mut f, a) = setup(1_000);
            for amt in [100u128, 200, 50] {
                f.transfer(a.bob, amt).unwrap();
            }
            let sum = f.balance_of(a.alice) + f.balance_of(a.bob) + f.balance_of(a.charlie);
            assert_eq!(sum, f.total_supply());
        }

        #[ink::test]
        fn mint_increases_supply_and_balance() {
            let (mut f, a) = setup(1_000);
            f.mint(a.bob, 250).unwrap();
            assert_eq!(f.total_supply(), 1_250);
            assert_eq!(f.balance_of(a.bob), 250);
            assert_eq!(f.balance_of(a.alice), 1_000); // unchanged
        }

        #[ink::test]
        fn burn_decreases_supply_and_balance() {
            let (mut f, a) = setup(1_000);
            set_caller(a.alice);
            f.burn(250).unwrap();
            assert_eq!(f.total_supply(), 750);
            assert_eq!(f.balance_of(a.alice), 750);
        }

        #[ink::test]
        fn burn_insufficient_balance() {
            let (mut f, a) = setup(100);
            set_caller(a.alice);
            assert_eq!(f.burn(200), Err(Error::InsufficientBalance));
        }

        #[ink::test]
        fn mint_burn_round_trip_preserves_supply() {
            let (mut f, a) = setup(1_000);
            f.mint(a.bob, 250).unwrap();
            set_caller(a.bob);
            f.burn(250).unwrap();
            assert_eq!(f.total_supply(), 1_000);
            assert_eq!(f.balance_of(a.bob), 0);
        }
    }
}
