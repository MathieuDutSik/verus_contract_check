#![cfg_attr(target_arch = "wasm32", no_main)]

mod state;

use fungible_linera::{FungibleAbi, InitialState, Message, Operation};
use linera_sdk::{
    base::{AccountOwner, WithContractAbi},
    views::{RootView, View},
    Contract, ContractRuntime,
};
use state::Fungible;

pub struct FungibleContract {
    state: Fungible,
    runtime: ContractRuntime<Self>,
}

linera_sdk::contract!(FungibleContract);

impl WithContractAbi for FungibleContract {
    type Abi = FungibleAbi;
}

impl Contract for FungibleContract {
    type Message = Message;
    type InstantiationArgument = InitialState;
    type Parameters = ();

    async fn load(runtime: ContractRuntime<Self>) -> Self {
        let state = Fungible::load(runtime.root_view_storage_context())
            .await
            .expect("load state");
        Self { state, runtime }
    }

    async fn instantiate(&mut self, argument: InitialState) {
        let mut total: u128 = 0;
        for (owner, amount) in argument.accounts.iter() {
            total = total.checked_add(*amount).expect("supply overflow");
            self.state.credit(*owner, *amount).await;
        }
        self.state.total_supply.set(total);
    }

    async fn execute_operation(&mut self, op: Operation) -> Self::Response {
        match op {
            Operation::Transfer { source, target, amount } => {
                self.assert_authorized(&source);
                self.state.debit(source, amount).await.expect("debit");
                self.state.credit(target, amount).await;
            }
        }
    }

    async fn execute_message(&mut self, message: Message) {
        match message {
            Message::Credit { target, amount } => {
                self.state.credit(target, amount).await;
            }
        }
    }

    async fn store(mut self) {
        self.state.save().await.expect("save state");
    }
}

impl FungibleContract {
    fn assert_authorized(&self, owner: &AccountOwner) {
        let signer = self.runtime.authenticated_signer().expect("signed op");
        assert_eq!(AccountOwner::from(signer), *owner, "unauthorized source");
    }
}
