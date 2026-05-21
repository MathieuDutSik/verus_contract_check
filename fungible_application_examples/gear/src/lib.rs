#![no_std]
extern crate alloc;

use gstd::{msg, prelude::*, ActorId};
use hashbrown::HashMap;
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
struct Fungible {
    total_supply: u128,
    balances: HashMap<ActorId, u128>,
}

static mut STATE: Option<Fungible> = None;

fn state() -> &'static mut Fungible {
    unsafe { STATE.as_mut().expect("uninitialized") }
}

#[no_mangle]
extern "C" fn init() {
    let cfg: InitConfig = msg::load().expect("init payload");
    let mut s = Fungible::default();
    s.total_supply = cfg.total_supply;
    s.balances.insert(cfg.owner, cfg.total_supply);
    unsafe { STATE = Some(s); }
}

#[no_mangle]
extern "C" fn handle() {
    let action: Action = msg::load().expect("handle payload");
    let from = msg::source();
    let s = state();
    match action {
        Action::Transfer { to, amount } => {
            let src = s.balances.get(&from).copied().unwrap_or(0);
            let src_next = src.checked_sub(amount).expect("insufficient balance");
            let dst = s.balances.get(&to).copied().unwrap_or(0);
            let dst_next = dst.checked_add(amount).expect("balance overflow");
            s.balances.insert(from, src_next);
            s.balances.insert(to, dst_next);
            msg::reply(Event::Transferred { from, to, amount }, 0).expect("reply");
        }
        Action::BalanceOf { account } => {
            let amount = s.balances.get(&account).copied().unwrap_or(0);
            msg::reply(Event::Balance { account, amount }, 0).expect("reply");
        }
    }
}
