#![cfg_attr(not(feature = "std"), no_std, no_main)]

#[ink::contract]
mod fungible {
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
            let from_next = from_balance.checked_sub(value).ok_or(Error::InsufficientBalance)?;
            let to_balance = self.balances.get(to).unwrap_or(0);
            let to_next = to_balance.checked_add(value).ok_or(Error::Overflow)?;
            self.balances.insert(from, &from_next);
            self.balances.insert(to, &to_next);
            self.env().emit_event(Transfer { from, to, value });
            Ok(())
        }
    }
}
