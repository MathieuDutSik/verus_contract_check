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
    }
}
