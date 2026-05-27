// Copyright (c) Zefchain Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

use linera_sdk::{
    linera_base_types::{AccountOwner, Amount, OwnerSpender},
    views::{linera_views, SyncMapView, SyncRootView, SyncViewStorageContext},
};

use crate::InitialState;

/// The application state.
#[derive(SyncRootView)]
#[view(context = SyncViewStorageContext)]
pub struct FungibleTokenState {
    pub accounts: SyncMapView<AccountOwner, Amount>,
    pub allowances: SyncMapView<OwnerSpender, Amount>,
}

#[allow(dead_code)]
impl FungibleTokenState {
    /// Initializes the application state with some accounts with initial balances.
    pub fn initialize_accounts(&mut self, state: InitialState) {
        for (k, v) in state.accounts {
            if v != Amount::ZERO {
                self.accounts
                    .insert(&k, v)
                    .expect("Error in insert statement");
            }
        }
    }

    /// Obtains the balance for an `account`, returning `None` if there's no entry for the account.
    pub fn balance(&self, account: &AccountOwner) -> Option<Amount> {
        self.accounts
            .get(account)
            .expect("Failure in the retrieval")
    }

    /// Obtains the balance for an `account`.
    pub fn balance_or_default(&self, account: &AccountOwner) -> Amount {
        self.balance(account).unwrap_or_default()
    }

    /// Credits an `account` with the provided `amount`.
    pub fn approve(&mut self, owner: AccountOwner, spender: AccountOwner, allowance: Amount) {
        let owner_spender = OwnerSpender::new(owner, spender);
        if allowance == Amount::ZERO {
            self.allowances
                .remove(&owner_spender)
                .expect("Failed to remove allowance");
            return;
        }
        let total_allowance = self
            .allowances
            .get_mut_or_default(&owner_spender)
            .expect("Failed allowance access");
        *total_allowance = allowance;
    }

    pub fn debit_for_transfer_from(
        &mut self,
        owner: AccountOwner,
        spender: AccountOwner,
        amount: Amount,
    ) {
        if amount == Amount::ZERO {
            return;
        }
        self.debit(owner, amount);
        let owner_spender = OwnerSpender::new(owner, spender);
        let mut allowance = self
            .allowances
            .get(&owner_spender)
            .expect("Failed allowance access")
            .unwrap_or_default();
        allowance.try_sub_assign(amount).unwrap_or_else(|_| {
            panic!("Spender {spender} does not have a sufficient from owner {owner} for transfer_from; allowance={allowance} amount={amount}")
        });
        if allowance == Amount::ZERO {
            self.allowances
                .remove(&owner_spender)
                .expect("Failed to remove an empty account");
        } else {
            self.allowances
                .insert(&owner_spender, allowance)
                .expect("Failed insertion operation");
        }
    }

    /// Credits an `account` with the provided `amount`. Forwards to the
    /// verified `crate::verified_state::verified_credit` kernel; the
    /// kernel's `ensures` clause pins the abstract effect on the
    /// `account_map_view` ghost projection.
    pub fn credit(&mut self, account: AccountOwner, amount: Amount) {
        crate::verified_state::verified_credit(&mut self.accounts, account, amount);
    }

    /// Tries to debit the requested `amount` from an `account`. Forwards
    /// to `verified_state::verified_debit`; on underflow (insufficient
    /// balance) the kernel returns `Err(())` and we panic — matching the
    /// previous direct-arithmetic behavior.
    pub fn debit(&mut self, account: AccountOwner, amount: Amount) {
        crate::verified_state::verified_debit(&mut self.accounts, account, amount)
            .unwrap_or_else(|()| {
                panic!("Source account {account} does not have sufficient balance for transfer")
            });
    }
}
