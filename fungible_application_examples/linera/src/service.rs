#![cfg_attr(target_arch = "wasm32", no_main)]

mod state;

use async_graphql::{EmptySubscription, Object, Schema};
use fungible_linera::FungibleAbi;
use linera_sdk::{
    base::{AccountOwner, WithServiceAbi},
    views::View,
    Service, ServiceRuntime,
};
use state::Fungible;
use std::sync::Arc;

pub struct FungibleService {
    state: Arc<Fungible>,
}

linera_sdk::service!(FungibleService);

impl WithServiceAbi for FungibleService {
    type Abi = FungibleAbi;
}

impl Service for FungibleService {
    type Parameters = ();

    async fn new(runtime: ServiceRuntime<Self>) -> Self {
        let state = Fungible::load(runtime.root_view_storage_context())
            .await
            .expect("load state");
        Self { state: Arc::new(state) }
    }

    async fn handle_query(&self, request: async_graphql::Request) -> async_graphql::Response {
        let schema = Schema::build(QueryRoot { state: self.state.clone() }, EmptyMutation, EmptySubscription).finish();
        schema.execute(request).await
    }
}

pub struct QueryRoot {
    state: Arc<Fungible>,
}

#[Object]
impl QueryRoot {
    async fn balance(&self, owner: AccountOwner) -> u128 {
        self.state.balance(&owner).await
    }

    async fn total_supply(&self) -> u128 {
        *self.state.total_supply.get()
    }
}

pub struct EmptyMutation;

#[Object]
impl EmptyMutation {
    async fn noop(&self) -> bool { true }
}
