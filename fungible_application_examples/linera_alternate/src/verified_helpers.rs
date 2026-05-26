// Verified u128-level arithmetic for the allowance / transfer_from machinery
// that `state.rs` exposes on top of the chain-agnostic `core.rs`.
//
// `state.rs` performs:
//   - `credit`               : balance += amount     (saturating in Linera, here checked)
//   - `debit`                : balance -= amount     (panics on underflow at runtime)
//   - `approve`              : allowance = new value (or remove if zero)
//   - `debit_for_transfer_from`
//                            : allowance -= amount; balance -= amount
//
// The functions below are the *verified arithmetic kernels* that the
// state-level operations reduce to once we strip away the storage layer
// (`SyncMapView`) and the `Amount` newtype. Each kernel carries the
// precondition that prevents the runtime panic, and an ensures clause that
// pins down the resulting value(s) in `nat` arithmetic so we can compose
// them with the conservation lemmas in `core.rs`.
//
// Verifying these as plain `u128 -> u128` functions is the same "shallow
// port" tier we use for ink!/MultiversX. A "deeper port" would replace
// `Amount` and `SyncMapView<K,V>` with `external_type_specification`
// wrappers and lift these obligations into proofs about
// `FungibleTokenState`; that is tracked in TODO.md.

use vstd::prelude::*;

verus! {

/// Verified `credit`: balance + amount, refusing overflow.
///
/// Linera's `Amount::saturating_add_assign` saturates at u128::MAX in
/// production. We require the caller to prove the sum stays in range,
/// which is the *honest* contract for a token that wants conservation
/// — saturation silently breaks `total_supply` invariants.
pub fn verified_credit(balance: u128, amount: u128) -> (r: u128)
    requires
        balance as nat + amount as nat <= u128::MAX as nat,
    ensures
        r as nat == balance as nat + amount as nat,
{
    balance + amount
}

/// Verified `debit`: balance - amount, with sufficient-funds precondition.
pub fn verified_debit(balance: u128, amount: u128) -> (r: u128)
    requires
        balance >= amount,
    ensures
        r as nat == balance as nat - amount as nat,
{
    balance - amount
}

/// Verified `approve`: set the allowance to the new value.
///
/// Trivial at the arithmetic level (Linera-style approve overwrites the
/// previous value rather than incrementing it), but recorded as a
/// verification obligation so the spec ties to a concrete u128 operation.
pub fn verified_approve(new_allowance: u128) -> (r: u128)
    ensures
        r == new_allowance,
{
    new_allowance
}

/// Verified `debit_for_transfer_from` (allowance side):
/// decrement the allowance, returning the new value.
pub fn verified_debit_allowance(allowance: u128, amount: u128) -> (r: u128)
    requires
        allowance >= amount,
    ensures
        r as nat == allowance as nat - amount as nat,
{
    allowance - amount
}

/// Verified transfer arithmetic between two distinct accounts:
/// debit `from`, credit `to`. Mirrors `core::transfer_balances` but
/// returns the new pair directly (the form needed at the state-layer
/// integration point).
pub fn verified_transfer_pair(
    from_balance: u128,
    to_balance: u128,
    amount: u128,
) -> (r: (u128, u128))
    requires
        from_balance >= amount,
        to_balance as nat + amount as nat <= u128::MAX as nat,
    ensures
        r.0 as nat == from_balance as nat - amount as nat,
        r.1 as nat == to_balance as nat + amount as nat,
        r.0 as nat + r.1 as nat == from_balance as nat + to_balance as nat,
{
    (from_balance - amount, to_balance + amount)
}

/// Verified full `transfer_from`: decrement allowance, debit owner,
/// credit recipient. The two conservation-flavoured ensures clauses
/// connect this to the `State<A>` invariant in `core.rs` once the
/// storage layer is lifted.
pub fn verified_transfer_from(
    allowance: u128,
    from_balance: u128,
    to_balance: u128,
    amount: u128,
) -> (r: (u128, u128, u128))
    requires
        allowance >= amount,
        from_balance >= amount,
        to_balance as nat + amount as nat <= u128::MAX as nat,
    ensures
        r.0 as nat == allowance as nat - amount as nat,
        r.1 as nat == from_balance as nat - amount as nat,
        r.2 as nat == to_balance as nat + amount as nat,
        // Conservation of the (from, to) total — independent of allowance.
        r.1 as nat + r.2 as nat == from_balance as nat + to_balance as nat,
{
    (allowance - amount, from_balance - amount, to_balance + amount)
}

} // verus!
