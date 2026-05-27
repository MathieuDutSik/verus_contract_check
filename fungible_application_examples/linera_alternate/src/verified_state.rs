// Verified kernels that state.rs's methods forward to.
//
// Same pattern as NEAR's `Fungible::transfer` -> `verified_transfer`:
// the contract's exposed method is a one-line forwarder; all of the
// substantive logic (read balance, do the arithmetic, write balance
// back) lives here with proven `ensures` clauses that pin the abstract
// effect on the ghost `account_map_view` / `allowance_map_view`.

use linera_sdk::linera_base_types::{Amount, AccountOwner};
use linera_sdk::views::SyncMapView;

use crate::linera_axioms::{
    amount_zero, amount_saturating_add_assign, amount_try_sub_assign,
    ax_account_get, ax_account_insert, ax_account_remove,
};

vstd::prelude::verus! {
    #[cfg(verus_only)]
    use vstd::prelude::*;
    #[cfg(verus_only)]
    use crate::linera_axioms::{amount_val, account_map_view};

    /// Verified `credit`: adds `amount` to `account`'s balance, saturating
    /// at `u128::MAX` (the linera SDK's `saturating_add_assign` semantics).
    /// On `amount == 0`, the map is unchanged.
    ///
    /// The abstract effect on `account_map_view` is fully pinned: the
    /// target account's new `amount_val` is exactly the saturating sum;
    /// every other entry's domain-presence and value are preserved.
    pub fn verified_credit(
        accounts: &mut SyncMapView<AccountOwner, Amount>,
        account:  AccountOwner,
        amount:   Amount,
    )
        ensures
            // No-op path.
            amount_val(amount) == 0 ==>
                account_map_view(final(accounts)) == account_map_view(old(accounts)),
            // Mutating path: target account ends up with saturating sum.
            amount_val(amount) != 0 ==>
                account_map_view(final(accounts)).dom().contains(account)
                && amount_val(account_map_view(final(accounts))[account]) == {
                    let prev: u128 = if account_map_view(old(accounts)).dom().contains(account) {
                        amount_val(account_map_view(old(accounts))[account])
                    } else { 0u128 };
                    if prev as int + amount_val(amount) as int <= u128::MAX as int {
                        (prev + amount_val(amount)) as u128
                    } else {
                        u128::MAX
                    }
                },
            // Other accounts unchanged.
            amount_val(amount) != 0 ==>
                forall|k: AccountOwner| #![auto]
                    k != account ==>
                        account_map_view(final(accounts)).dom().contains(k)
                            == account_map_view(old(accounts)).dom().contains(k)
                        && (account_map_view(final(accounts)).dom().contains(k) ==>
                            account_map_view(final(accounts))[k]
                                == account_map_view(old(accounts))[k]),
    {
        if amount == amount_zero() {
            return;
        }
        let mut balance = match ax_account_get(accounts, &account) {
            Some(b) => b,
            None    => amount_zero(),
        };
        amount_saturating_add_assign(&mut balance, amount);
        ax_account_insert(accounts, &account, balance);
    }

    /// Verified `debit`: subtracts `amount` from `account`'s balance.
    /// Returns `Err(())` on underflow (insufficient balance); the
    /// state.rs forwarder panics on that path. On success, if the result
    /// is zero the entry is removed; otherwise the new value is written.
    /// `amount == 0` is a no-op (matches state.rs).
    pub fn verified_debit(
        accounts: &mut SyncMapView<AccountOwner, Amount>,
        account:  AccountOwner,
        amount:   Amount,
    ) -> (r: Result<(), ()>)
        ensures
            match r {
                Ok(()) =>
                    // No-op path: amount == 0 leaves the map unchanged.
                    (amount_val(amount) == 0 ==>
                        account_map_view(final(accounts)) == account_map_view(old(accounts)))
                    // Mutating path: caller had sufficient balance.
                    && (amount_val(amount) != 0 ==> {
                        let prev: u128 = if account_map_view(old(accounts)).dom().contains(account) {
                            amount_val(account_map_view(old(accounts))[account])
                        } else { 0u128 };
                        prev >= amount_val(amount)
                    }),
                Err(()) =>
                    amount_val(amount) != 0
                    && {
                        let prev: u128 = if account_map_view(old(accounts)).dom().contains(account) {
                            amount_val(account_map_view(old(accounts))[account])
                        } else { 0u128 };
                        prev < amount_val(amount)
                    },
            },
    {
        if amount == amount_zero() {
            return Ok(());
        }
        let mut balance = match ax_account_get(accounts, &account) {
            Some(b) => b,
            None    => amount_zero(),
        };
        match amount_try_sub_assign(&mut balance, amount) {
            Ok(())  => {}
            Err(()) => return Err(()),
        }
        if balance == amount_zero() {
            ax_account_remove(accounts, &account);
        } else {
            ax_account_insert(accounts, &account, balance);
        }
        Ok(())
    }

    // verified_approve and verified_debit_for_transfer_from are deferred —
    // both require OwnerSpender::new, which panics on owner == spender.
    // That brings in a divergence-axiom (panic_str with `ensures false`)
    // plus a spec-level injective constructor — possible but bigger
    // scope. Tracked in TODO.md.
}
