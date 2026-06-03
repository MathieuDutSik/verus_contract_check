// Verified arithmetic helpers that the `#[ink(message)]` methods of
// the fungible contract forward to.
//
// Lives outside the `#[ink::contract]` module (matching the macro
// constraint that Verus can't parse the expanded module body). The
// helpers cover the mint/burn arithmetic + supply update; transfer's
// arithmetic is already covered by `core::transfer_balances` in the
// shared crate.
//
// Same shape as `verified_state.rs` in the linera_alternate fungible
// example: the `#[ink(message)]` body is a thin forwarder; the
// arithmetic with its `ensures` clause lives here.

pub use verus_fungible_core::TransferError;

vstd::prelude::verus! {
    #[cfg(verus_only)]
    use vstd::prelude::*;

    /// Verified mint arithmetic: `to_balance' = to_balance + amount` and
    /// `total_supply' = total_supply + amount` on success.
    pub fn verified_mint_step(
        to_balance:   u128,
        total_supply: u128,
        amount:       u128,
    ) -> (r: Result<(u128, u128), TransferError>)
        ensures
            match r {
                Ok((new_bal, new_supply)) =>
                    new_bal    == (to_balance   + amount) as u128
                    && new_supply == (total_supply + amount) as u128,
                Err(_) => true,
            },
    {
        let new_supply = match total_supply.checked_add(amount) {
            Some(v) => v,
            None    => return Err(TransferError::Overflow),
        };
        let new_bal = match to_balance.checked_add(amount) {
            Some(v) => v,
            None    => return Err(TransferError::Overflow),
        };
        Ok((new_bal, new_supply))
    }

    /// Verified burn arithmetic: `from_balance' = from_balance - amount` and
    /// `total_supply' = total_supply - amount` on success.
    pub fn verified_burn_step(
        from_balance: u128,
        total_supply: u128,
        amount:       u128,
    ) -> (r: Result<(u128, u128), TransferError>)
        ensures
            match r {
                Ok((new_bal, new_supply)) =>
                    new_bal      == (from_balance - amount) as u128
                    && new_supply == (total_supply - amount) as u128,
                Err(_) => true,
            },
    {
        let new_bal = match from_balance.checked_sub(amount) {
            Some(v) => v,
            None    => return Err(TransferError::Insufficient),
        };
        let new_supply = match total_supply.checked_sub(amount) {
            Some(v) => v,
            None    => return Err(TransferError::InsufficientSupply),
        };
        Ok((new_bal, new_supply))
    }
}
