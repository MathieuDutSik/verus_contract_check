// Verified BigUint transfer kernel that the MultiversX `transfer`
// endpoint forwards to.
//
// Lives outside the `#[multiversx_sc::contract]` macro module (Verus
// can't parse the expansion of that macro). Same shape as
// `verified_state.rs` in the linera_alternate fungible example.

use crate::mvx_axioms::{biguint_add_assign, biguint_ge, biguint_sub};
use multiversx_sc::api::ManagedTypeApi;
use multiversx_sc::types::BigUint;

vstd::prelude::verus! {
    #[cfg(verus_only)]
    use vstd::prelude::*;
    #[cfg(verus_only)]
    use crate::mvx_axioms::biguint_val;

    /// Verified BigUint transfer: returns the new (from, to) balance pair
    /// such that `from_next + to_next == from_balance + to_balance` and
    /// each side moves by exactly `amount`. Fails with `Err(())` on
    /// underflow.
    ///
    /// No overflow precondition — BigUint is unbounded by construction, so
    /// addition is unconditional. The `u128` version in `fungible_core`
    /// must check `to_balance + amount <= u128::MAX`; the BigUint version
    /// does not.
    pub fn verified_transfer_big<M: ManagedTypeApi>(
        from_balance: BigUint<M>,
        to_balance:   BigUint<M>,
        amount:       &BigUint<M>,
    ) -> (r: Result<(BigUint<M>, BigUint<M>), ()>)
        ensures
            match r {
                Ok((from_next, to_next)) =>
                    biguint_val(&from_next) + biguint_val(&to_next)
                        == biguint_val(&from_balance) + biguint_val(&to_balance)
                    && biguint_val(&from_next)
                        == (biguint_val(&from_balance) - biguint_val(amount)) as nat
                    && biguint_val(&to_next)
                        == biguint_val(&to_balance) + biguint_val(amount),
                Err(()) =>
                    biguint_val(&from_balance) < biguint_val(amount),
            },
    {
        if !biguint_ge(&from_balance, amount) {
            return Err(());
        }
        let from_next = biguint_sub(from_balance, amount);
        let mut to_next = to_balance;
        biguint_add_assign(&mut to_next, amount);
        Ok((from_next, to_next))
    }
}
