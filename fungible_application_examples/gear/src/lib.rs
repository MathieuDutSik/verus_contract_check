// Gear fungible-token program with Verus-verified core arithmetic.
//
// Layout (mirrors `linera_alternate` fungible):
//   - `pub mod core;`              — chain-agnostic verified core.
//   - `pub mod gear_axioms;`       — ActorId external type +
//                                    `msg::source()` wrapper + ghost.
//   - `pub mod verified_helpers;`  — `AxHashMap<K, V>` wrapper +
//                                    `view_map` ghost + `read_balance` /
//                                    `save_balance` axioms +
//                                    `apply_transfer` /
//                                    `verified_transfer` kernels.
//   - this file                    — `Fungible` struct + scale codec
//                                    message types + `extern "C"`
//                                    `init`/`handle` entry points +
//                                    tests.

#![cfg_attr(not(test), no_std)]
extern crate alloc;

pub mod core;
pub mod gear_axioms;
pub mod verified_helpers;

use crate::verified_helpers::{
    apply_transfer, read_balance, save_balance, verified_transfer, AxHashMap,
};
use gstd::{msg, prelude::*, ActorId};
use parity_scale_codec::{Decode, Encode};
use scale_info::TypeInfo;

#[derive(Encode, Decode, TypeInfo)]
pub struct InitConfig {
    pub owner: ActorId,
    pub total_supply: u128,
}

#[derive(Encode, Decode, TypeInfo)]
pub enum Action {
    Transfer { to: ActorId, amount: u128 },
    BalanceOf { account: ActorId },
}

#[derive(Encode, Decode, TypeInfo)]
pub enum Event {
    Transferred { from: ActorId, to: ActorId, amount: u128 },
    Balance { account: ActorId, amount: u128 },
}



#[derive(Default)]
pub struct Fungible {
    pub total_supply: u128,
    pub balances: AxHashMap<ActorId, u128>,
}

impl Fungible {
    pub fn init(owner: ActorId, total_supply: u128) -> Self {
        let mut s = Self::default();
        s.total_supply = total_supply;
        save_balance(&mut s.balances, owner, total_supply);
        s
    }

    pub fn balance_of(&self, account: &ActorId) -> u128 {
        read_balance(&self.balances, account)
    }

    /// Test-only entry point. Production code goes through
    /// `verified_transfer` (which reads the sender from the runtime via
    /// `msg::source()`). Tests need to inject a sender, so this thin
    /// wrapper forwards to the same verified `apply_transfer` kernel and
    /// maps the closed `TransferError` enum back to a string.
    pub fn do_transfer(&mut self, from: ActorId, to: ActorId, amount: u128) -> Result<(), &'static str> {
        match apply_transfer(&mut self.balances, from, to, amount) {
            Ok(())                              => Ok(()),
            Err(TransferError::SelfTransfer)    => Err("self-transfer"),
            Err(TransferError::Insufficient)    => Err("insufficient balance"),
            Err(TransferError::Overflow)        => Err("balance overflow"),
            // Variants the gear contract doesn't construct.
            Err(_)                              => Err("transfer failed"),
        }
    }
}

pub use verus_fungible_core::TransferError;


static mut STATE: Option<Fungible> = None;

fn state() -> &'static mut Fungible {
    #[allow(static_mut_refs)]
    unsafe { STATE.as_mut().expect("uninitialized") }
}

#[no_mangle]
extern "C" fn init() {
    let cfg: InitConfig = msg::load().expect("init payload");
    unsafe { STATE = Some(Fungible::init(cfg.owner, cfg.total_supply)); }
}

#[no_mangle]
extern "C" fn handle() {
    let action: Action = msg::load().expect("handle payload");
    let s = state();
    match action {
        Action::Transfer { to, amount } => {
            // Routes through the verified kernel. Sender is read inside
            // `verified_transfer` via the axiomatized `msg::source()` wrapper.
            let from = msg::source();
            verified_transfer(&mut s.balances, to, amount).expect("transfer");
            msg::reply(Event::Transferred { from, to, amount }, 0).expect("reply");
        }
        Action::BalanceOf { account } => {
            let amount = s.balance_of(&account);
            msg::reply(Event::Balance { account, amount }, 0).expect("reply");
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn id(b: u8) -> ActorId { ActorId::new([b; 32]) }

    fn setup(supply: u128) -> (Fungible, ActorId, ActorId, ActorId) {
        let owner = id(1);
        let alice = id(2);
        let bob   = id(3);
        (Fungible::init(owner, supply), owner, alice, bob)
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
