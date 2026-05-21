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
    pub accounts: BTreeMap<AccountOwner, u128>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum Operation {
    Transfer {
        source: AccountOwner,
        target: AccountOwner,
        amount: u128,
    },
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum Message {
    Credit { target: AccountOwner, amount: u128 },
}
