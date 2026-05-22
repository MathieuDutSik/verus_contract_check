use linera_sdk::base::AccountOwner;
use linera_sdk::views::{linera_views, MapView, RegisterView, RootView, ViewStorageContext};

#[derive(RootView, async_graphql::SimpleObject)]
#[view(context = "ViewStorageContext")]
pub struct Fungible {
    pub total_supply: RegisterView<u64>,
    pub balances: MapView<AccountOwner, u64>,
}

#[allow(dead_code)] // credit/debit used by contract binary only; service binary reads
impl Fungible {
    pub async fn balance(&self, owner: &AccountOwner) -> u64 {
        self.balances.get(owner).await.unwrap_or_default().unwrap_or(0)
    }

    pub async fn credit(&mut self, owner: AccountOwner, amount: u64) {
        let current = self.balance(&owner).await;
        let next = current.checked_add(amount).expect("balance overflow");
        self.balances.insert(&owner, next).unwrap();
    }

    pub async fn debit(&mut self, owner: AccountOwner, amount: u64) -> Result<(), &'static str> {
        let current = self.balance(&owner).await;
        let next = current.checked_sub(amount).ok_or("insufficient balance")?;
        self.balances.insert(&owner, next).unwrap();
        Ok(())
    }
}
