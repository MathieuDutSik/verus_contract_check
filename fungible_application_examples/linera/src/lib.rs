use async_graphql::{Request, Response, SimpleObject};
use linera_sdk::base::{AccountOwner, ContractAbi, ServiceAbi};
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;

pub struct FungibleAbi;

impl ContractAbi for FungibleAbi {
    type Operation = Operation;
    type Response = ();
}

impl ServiceAbi for FungibleAbi {
    type Query = Request;
    type QueryResponse = Response;
}

#[derive(Clone, Debug, Serialize, Deserialize, SimpleObject)]
pub struct InitialState {
    pub accounts: BTreeMap<AccountOwner, u64>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum Operation {
    Transfer {
        source: AccountOwner,
        target: AccountOwner,
        amount: u64,
    },
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum Message {
    Credit { target: AccountOwner, amount: u64 },
}

// Pure-logic tests. The actual contract uses linera-sdk's View framework
// (MapView/RegisterView), which needs a ViewStorageContext to exercise.
// Rather than spinning up MemoryStorage, we mirror the contract logic
// against plain types — same pattern as the multiversx / solana / ic /
// gear examples in this repo. Keep these in lockstep with state.rs and
// contract.rs.
#[cfg(test)]
mod tests {
    use linera_sdk::base::{AccountOwner, Owner};
    use linera_sdk::base::CryptoHash;
    use std::collections::BTreeMap;

    struct State {
        total_supply: u64,
        balances: BTreeMap<AccountOwner, u64>,
    }

    impl State {
        fn init(owner: AccountOwner, supply: u64) -> Self {
            let mut balances = BTreeMap::new();
            balances.insert(owner, supply);
            Self { total_supply: supply, balances }
        }
        fn balance_of(&self, owner: &AccountOwner) -> u64 {
            self.balances.get(owner).copied().unwrap_or(0)
        }
        fn do_transfer(&mut self, from: AccountOwner, to: AccountOwner, amount: u64) -> Result<(), &'static str> {
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

    fn owner(b: u8) -> AccountOwner {
        let h = CryptoHash::from([b as u64, 0, 0, 0]);
        AccountOwner::User(Owner(h))
    }

    fn setup(supply: u64) -> (State, AccountOwner, AccountOwner, AccountOwner) {
        (State::init(owner(1), supply), owner(1), owner(2), owner(3))
    }

    #[test]
    fn init_supply_credited_to_owner() {
        let (s, o, _, _) = setup(1_000);
        assert_eq!(s.total_supply, 1_000);
        assert_eq!(s.balance_of(&o), 1_000);
    }

    #[test]
    fn balance_of_unknown_is_zero() {
        let (s, _, _, _) = setup(1_000);
        assert_eq!(s.balance_of(&owner(42)), 0);
    }

    #[test]
    fn transfer_happy_path() {
        let (mut s, o, a, _) = setup(1_000);
        s.do_transfer(o, a, 250).unwrap();
        assert_eq!(s.balance_of(&o), 750);
        assert_eq!(s.balance_of(&a), 250);
    }

    #[test]
    fn transfer_insufficient_balance() {
        let (mut s, o, a, _) = setup(100);
        assert_eq!(s.do_transfer(o, a, 200), Err("insufficient balance"));
    }

    #[test]
    fn self_transfer_rejected() {
        let (mut s, o, _, _) = setup(1_000);
        assert_eq!(s.do_transfer(o, o, 10), Err("self-transfer"));
    }

    #[test]
    fn total_supply_invariant_after_transfer() {
        let (mut s, o, a, b) = setup(1_000);
        for amt in [100u64, 200, 50] {
            s.do_transfer(o, a, amt).unwrap();
        }
        let sum = s.balance_of(&o) + s.balance_of(&a) + s.balance_of(&b);
        assert_eq!(sum, s.total_supply);
    }
}
