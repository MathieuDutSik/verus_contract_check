#![no_std]

multiversx_sc::imports!();

#[multiversx_sc::contract]
pub trait Fungible {
    #[init]
    fn init(&self, total_supply: BigUint) {
        let caller = self.blockchain().get_caller();
        self.total_supply().set(&total_supply);
        self.balances(&caller).set(&total_supply);
    }

    #[endpoint]
    fn transfer(&self, to: ManagedAddress, amount: BigUint) {
        let from = self.blockchain().get_caller();
        require!(from != to, "self-transfer");
        let from_balance = self.balances(&from).get();
        require!(from_balance >= amount, "insufficient balance");
        self.balances(&from).set(&(from_balance - &amount));
        self.balances(&to).update(|b| *b += &amount);
    }

    #[view(balanceOf)]
    fn balance_of(&self, account: ManagedAddress) -> BigUint {
        self.balances(&account).get()
    }

    #[view(totalSupply)]
    #[storage_mapper("totalSupply")]
    fn total_supply(&self) -> SingleValueMapper<BigUint>;

    #[storage_mapper("balances")]
    fn balances(&self, account: &ManagedAddress) -> SingleValueMapper<BigUint>;
}
