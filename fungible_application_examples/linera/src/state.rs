use linera_sdk::base::AccountOwner;
use linera_sdk::views::{linera_views, MapView, RegisterView, RootView, ViewStorageContext};

#[derive(RootView, async_graphql::SimpleObject)]
#[view(context = "ViewStorageContext")]
pub struct Fungible {
    pub total_supply: RegisterView<u128>,
    pub balances: MapView<AccountOwner, u128>,
}

impl Fungible {
    pub async fn balance(&self, owner: &AccountOwner) -> u128 {
        self.balances.get(owner).await.unwrap_or_default().unwrap_or(0)
    }

    pub async fn credit(&mut self, owner: AccountOwner, amount: u128) {
        let current = self.balance(&owner).await;
        let next = current.checked_add(amount).expect("balance overflow");
        self.balances.insert(&owner, next).unwrap();
    }

    pub async fn debit(&mut self, owner: AccountOwner, amount: u128) -> Result<(), &'static str> {
        let current = self.balance(&owner).await;
        let next = current.checked_sub(amount).ok_or("insufficient balance")?;
        self.balances.insert(&owner, next).unwrap();
        Ok(())
    }
}
