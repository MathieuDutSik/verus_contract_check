use candid::{CandidType, Principal};
use ic_cdk::api::caller;
use ic_cdk_macros::{init, query, update};
use serde::Deserialize;
use std::cell::RefCell;
use std::collections::BTreeMap;

#[derive(Default, CandidType, Deserialize)]
pub struct State {
    pub total_supply: u128,
    pub balances: BTreeMap<Principal, u128>,
}

impl State {
    pub fn init(owner: Principal, total_supply: u128) -> Self {
        let mut s = Self::default();
        s.total_supply = total_supply;
        s.balances.insert(owner, total_supply);
        s
    }

    pub fn balance_of(&self, account: &Principal) -> u128 {
        self.balances.get(account).copied().unwrap_or(0)
    }

    pub fn do_transfer(&mut self, from: Principal, to: Principal, amount: u128) -> Result<(), String> {
        if from == to { return Err("self-transfer".into()); }
        let src = self.balance_of(&from);
        let src_next = src.checked_sub(amount).ok_or("insufficient balance")?;
        let dst = self.balance_of(&to);
        let dst_next = dst.checked_add(amount).ok_or("balance overflow")?;
        self.balances.insert(from, src_next);
        self.balances.insert(to, dst_next);
        Ok(())
    }
}

thread_local! { static STATE: RefCell<State> = RefCell::new(State::default()); }

#[init]
fn init(owner: Principal, total_supply: u128) {
    STATE.with(|s| *s.borrow_mut() = State::init(owner, total_supply));
}

#[query]
fn balance_of(account: Principal) -> u128 {
    STATE.with(|s| s.borrow().balance_of(&account))
}

#[query]
fn total_supply() -> u128 {
    STATE.with(|s| s.borrow().total_supply)
}

#[update]
fn transfer(to: Principal, amount: u128) -> Result<(), String> {
    let from = caller();
    STATE.with(|s| s.borrow_mut().do_transfer(from, to, amount))
}

ic_cdk::export_candid!();

#[cfg(test)]
mod tests {
    use super::*;

    fn p(b: u8) -> Principal { Principal::from_slice(&[b; 29]) }

    fn setup(supply: u128) -> (State, Principal, Principal, Principal) {
        let owner = p(1);
        let alice = p(2);
        let bob   = p(3);
        (State::init(owner, supply), owner, alice, bob)
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
        assert_eq!(s.balance_of(&p(42)), 0);
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
        assert_eq!(s.do_transfer(owner, alice, 200), Err("insufficient balance".into()));
    }

    #[test]
    fn self_transfer_rejected() {
        let (mut s, owner, _, _) = setup(1_000);
        assert_eq!(s.do_transfer(owner, owner, 10), Err("self-transfer".into()));
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
