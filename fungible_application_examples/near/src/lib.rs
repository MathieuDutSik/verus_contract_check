use near_sdk::store::LookupMap;
use near_sdk::{env, near, require, AccountId, BorshStorageKey, PanicOnDefault};

#[derive(BorshStorageKey)]
#[near(serializers = [borsh])]
enum StorageKey { Balances }

#[near(contract_state)]
#[derive(PanicOnDefault)]
pub struct Fungible {
    total_supply: u128,
    balances: LookupMap<AccountId, u128>,
}

#[near]
impl Fungible {
    #[init]
    pub fn new(owner: AccountId, total_supply: u128) -> Self {
        let mut balances = LookupMap::new(StorageKey::Balances);
        balances.insert(owner, total_supply);
        Self { total_supply, balances }
    }

    pub fn balance_of(&self, account: AccountId) -> u128 {
        self.balances.get(&account).copied().unwrap_or(0)
    }

    pub fn total_supply(&self) -> u128 { self.total_supply }

    pub fn transfer(&mut self, receiver: AccountId, amount: u128) {
        let sender = env::predecessor_account_id();
        require!(sender != receiver, "self-transfer");
        let from = self.balances.get(&sender).copied().unwrap_or(0);
        let from_next = from.checked_sub(amount).expect("insufficient balance");
        let to = self.balances.get(&receiver).copied().unwrap_or(0);
        let to_next = to.checked_add(amount).expect("balance overflow");
        self.balances.insert(sender, from_next);
        self.balances.insert(receiver, to_next);
    }
}
