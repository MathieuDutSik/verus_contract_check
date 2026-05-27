#![cfg_attr(not(test), no_std)]

// Chain-agnostic verified core (Layer 1): arithmetic + State<A> + conservation
// lemmas. Lives outside the `#[multiversx_sc::contract]` macro module so
// Verus can parse it.
#[path = "core.rs"]
pub mod fungible_core;

// BigUint axiomatization is blocked on Verus's external_trait_specification
// one-bound restriction. See mvx_axioms.rs for the analysis.

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

// Pure-logic tests. The multiversx framework's BigUint / ManagedAddress /
// SingleValueMapper require either a generated proxy (sc-meta) or a
// ScenarioWorld harness to exercise in-process. Rather than pulling that
// in, we mirror the contract's logic against plain types and test the
// algorithm. Keep the contract above and these tests in lockstep when
// editing.
#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    type Addr = [u8; 32];

    #[derive(Default)]
    struct State {
        total_supply: u128,
        balances: BTreeMap<Addr, u128>,
    }

    impl State {
        fn init(owner: Addr, supply: u128) -> Self {
            let mut s = Self::default();
            s.total_supply = supply;
            s.balances.insert(owner, supply);
            s
        }
        fn balance_of(&self, who: &Addr) -> u128 {
            self.balances.get(who).copied().unwrap_or(0)
        }
        fn do_transfer(&mut self, from: Addr, to: Addr, amount: u128) -> Result<(), &'static str> {
            if from == to { return Err("self-transfer"); }
            let src = self.balance_of(&from);
            let src_next = src.checked_sub(amount).ok_or("insufficient balance")?;
            let dst = self.balance_of(&to);
            let dst_next = dst.checked_add(amount).ok_or("balance overflow")?;
            self.balances.insert(from, src_next);
            self.balances.insert(to, dst_next);
            Ok(())
        }
    }

    fn id(b: u8) -> Addr { [b; 32] }

    fn setup(supply: u128) -> (State, Addr, Addr, Addr) {
        (State::init(id(1), supply), id(1), id(2), id(3))
    }

    #[test]
    fn init_supply_credited_to_owner() {
        let (s, owner, _, _) = setup(1_000);
        assert_eq!(s.total_supply, 1_000);
        assert_eq!(s.balance_of(&owner), 1_000);
    }

    #[test]
    fn balance_of_unknown_is_zero() {
        let (s, _, _, _) = setup(1_000);
        assert_eq!(s.balance_of(&id(42)), 0);
    }

    #[test]
    fn transfer_happy_path() {
        let (mut s, owner, alice, _) = setup(1_000);
        s.do_transfer(owner, alice, 250).unwrap();
        assert_eq!(s.balance_of(&owner), 750);
        assert_eq!(s.balance_of(&alice), 250);
    }

    #[test]
    fn transfer_insufficient_balance() {
        let (mut s, owner, alice, _) = setup(100);
        assert_eq!(s.do_transfer(owner, alice, 200), Err("insufficient balance"));
    }

    #[test]
    fn self_transfer_rejected() {
        let (mut s, owner, _, _) = setup(1_000);
        assert_eq!(s.do_transfer(owner, owner, 10), Err("self-transfer"));
    }

    #[test]
    fn total_supply_invariant_after_transfer() {
        let (mut s, owner, alice, bob) = setup(1_000);
        for amt in [100u128, 200, 50] {
            s.do_transfer(owner, alice, amt).unwrap();
        }
        let sum = s.balance_of(&owner) + s.balance_of(&alice) + s.balance_of(&bob);
        assert_eq!(sum, s.total_supply);
    }
}
