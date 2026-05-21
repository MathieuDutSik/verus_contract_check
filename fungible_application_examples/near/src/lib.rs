use near_sdk::borsh::{self, BorshDeserialize, BorshSerialize};
use near_sdk::collections::LookupMap;
use near_sdk::{env, near_bindgen, require, AccountId, BorshStorageKey, PanicOnDefault};

#[derive(BorshSerialize, BorshStorageKey)]
enum StorageKey { Balances }

#[near_bindgen]
#[derive(BorshDeserialize, BorshSerialize, PanicOnDefault)]
pub struct Fungible {
    total_supply: u128,
    balances: LookupMap<AccountId, u128>,
}

#[near_bindgen]
impl Fungible {
    #[init]
    pub fn new(owner: AccountId, total_supply: u128) -> Self {
        let mut balances = LookupMap::new(StorageKey::Balances);
        balances.insert(&owner, &total_supply);
        Self { total_supply, balances }
    }

    pub fn balance_of(&self, account: AccountId) -> u128 {
        self.balances.get(&account).unwrap_or(0)
    }

    pub fn total_supply(&self) -> u128 { self.total_supply }

    pub fn transfer(&mut self, receiver: AccountId, amount: u128) {
        let sender = env::predecessor_account_id();
        require!(sender != receiver, "self-transfer");
        let from = self.balances.get(&sender).unwrap_or(0);
        let from_next = from.checked_sub(amount).expect("insufficient balance");
        let to = self.balances.get(&receiver).unwrap_or(0);
        let to_next = to.checked_add(amount).expect("balance overflow");
        self.balances.insert(&sender, &from_next);
        self.balances.insert(&receiver, &to_next);
    }
}
