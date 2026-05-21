use candid::{CandidType, Principal};
use ic_cdk::api::caller;
use ic_cdk_macros::{init, query, update};
use serde::Deserialize;
use std::cell::RefCell;
use std::collections::BTreeMap;

#[derive(Default, CandidType, Deserialize)]
struct State {
    total_supply: u128,
    balances: BTreeMap<Principal, u128>,
}

thread_local! { static STATE: RefCell<State> = RefCell::new(State::default()); }

#[init]
fn init(owner: Principal, total_supply: u128) {
    STATE.with(|s| {
        let mut s = s.borrow_mut();
        s.total_supply = total_supply;
        s.balances.insert(owner, total_supply);
    });
}

#[query]
fn balance_of(account: Principal) -> u128 {
    STATE.with(|s| s.borrow().balances.get(&account).copied().unwrap_or(0))
}

#[query]
fn total_supply() -> u128 {
    STATE.with(|s| s.borrow().total_supply)
}

#[update]
fn transfer(to: Principal, amount: u128) -> Result<(), String> {
    let from = caller();
    if from == to { return Err("self-transfer".into()); }
    STATE.with(|s| {
        let mut s = s.borrow_mut();
        let src = *s.balances.get(&from).unwrap_or(&0);
        let src_next = src.checked_sub(amount).ok_or("insufficient balance")?;
        let dst = *s.balances.get(&to).unwrap_or(&0);
        let dst_next = dst.checked_add(amount).ok_or("balance overflow")?;
        s.balances.insert(from, src_next);
        s.balances.insert(to, dst_next);
        Ok(())
    })
}

ic_cdk::export_candid!();
