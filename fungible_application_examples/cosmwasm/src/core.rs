// Pure fungible-token logic, verified with Verus.
//
// Two layers of guarantee in this module:
//
// 1. `transfer_balances` — exec function on plain u128s.
//    Proves: on success, the two balances sum to the same value as before.
//    This is what `Fungible::transfer` calls at runtime (via the
//    `apply_transfer` helper in lib.rs).
//
// 2. `State<A>` + `state_after_transfer` + lemmas
//    — spec-level model, generic over the account-identifier type `A`.
//    Proves: with the invariant `sum_balances(balances) == total_supply`,
//    a transfer between two existing accounts preserves the invariant,
//    plus several supporting properties.
//
// Layer (1) is the executable arithmetic. Layer (2) is the global
// conservation property over an arbitrary number of accounts.
// The state type is generic in `A` so each chain can instantiate it
// with its own account-identifier (e.g. `near_sdk::AccountId`,
// `cosmwasm_std::Addr`).

use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::map::*;

verus! {

// -- Layer 1: executable transfer arithmetic ----------------------------

pub fn transfer_balances(
    from_balance: u128,
    to_balance: u128,
    amount: u128,
) -> (r: Result<(u128, u128), &'static str>)
    ensures
        match r {
            // Success: the two new balances sum to the same value as the
            // original two, and each is exactly `from - amount` / `to + amount`.
            Ok((from_next, to_next)) =>
                from_next + to_next == from_balance + to_balance
                && from_next == from_balance - amount
                && to_next == to_balance + amount,
            // Failure: exactly one of the two failure conditions must hold.
            Err(_) =>
                from_balance < amount
                || to_balance + amount > u128::MAX,
        },
{
    match from_balance.checked_sub(amount) {
        None => Err("insufficient balance"),
        Some(from_next) => match to_balance.checked_add(amount) {
            None => Err("balance overflow"),
            Some(to_next) => Ok((from_next, to_next)),
        },
    }
}

// -- Layer 2: spec-level State and conservation -------------------------

#[verifier::reject_recursive_types(A)]
pub struct State<A> {
    pub total_supply: nat,
    pub balances: Map<A, nat>,
}

/// Recursive sum of all balance values in the map.
pub open spec fn sum_balances<A>(m: Map<A, nat>) -> nat
    decreases m.dom().len() when m.dom().finite()
{
    if m.dom().finite() && m.dom().len() == 0 {
        0nat
    } else {
        let k = m.dom().choose();
        m[k] + sum_balances(m.remove(k))
    }
}

impl<A> State<A> {
    /// Conservation invariant: book-balance equals declared supply,
    /// and the domain is finite (needed for sum to be well-defined).
    pub open spec fn invariant(self) -> bool {
        self.balances.dom().finite()
        && sum_balances(self.balances) == self.total_supply
    }
}

/// New state after `amount` moves from `from` to `to`.
pub open spec fn state_after_transfer<A>(s: State<A>, from: A, to: A, amount: nat) -> State<A>
    recommends
        from != to,
        s.balances.dom().contains(from),
        s.balances.dom().contains(to),
        s.balances[from] >= amount,
{
    let f = s.balances[from];
    let t = s.balances[to];
    State {
        total_supply: s.total_supply,
        balances: s.balances
            .insert(from, (f - amount) as nat)
            .insert(to,   (t + amount) as nat),
    }
}

/// Lemma: replacing a present key's value shifts the sum by the delta.
pub proof fn lemma_sum_after_insert<A>(m: Map<A, nat>, k: A, v_new: nat)
    requires
        m.dom().finite(),
        m.dom().contains(k),
    ensures
        sum_balances(m.insert(k, v_new)) + m[k] == sum_balances(m) + v_new,
    decreases m.dom().len()
{
    let m2 = m.insert(k, v_new);
    // Domain is unchanged because k is already present.
    assert(m2.dom() =~= m.dom());

    let k0 = m.dom().choose();
    // Same set ⇒ same `choose` result, so both unfoldings pick `k0`.
    assert(m2.dom().choose() == k0);

    if k0 == k {
        assert(m2.remove(k) =~= m.remove(k));
    } else {
        assert(m.remove(k0).dom().contains(k));
        assert(m.remove(k0)[k] == m[k]);
        lemma_sum_after_insert(m.remove(k0), k, v_new);
        assert(m2.remove(k0) =~= m.remove(k0).insert(k, v_new));
    }
}

/// Main theorem: a transfer between two distinct present accounts
/// preserves the conservation invariant.
pub proof fn lemma_transfer_preserves_invariant<A>(
    s: State<A>,
    from: A,
    to: A,
    amount: nat,
)
    requires
        s.invariant(),
        from != to,
        s.balances.dom().contains(from),
        s.balances.dom().contains(to),
        s.balances[from] >= amount,
    ensures
        state_after_transfer(s, from, to, amount).invariant(),
{
    let f = s.balances[from];
    let t = s.balances[to];
    let m0 = s.balances;
    let m1 = m0.insert(from, (f - amount) as nat);
    let m2 = m1.insert(to,   (t + amount) as nat);

    lemma_sum_after_insert(m0, from, (f - amount) as nat);
    assert(m1.dom().contains(to));
    assert(m1[to] == t);
    lemma_sum_after_insert(m1, to, (t + amount) as nat);

    assert(m2.dom().finite());
}

// -- Tightening lemmas (#2, #3, #4) -------------------------------------

/// (#4) The supply field is invariant under transfer.
pub proof fn lemma_transfer_preserves_total_supply<A>(
    s: State<A>, from: A, to: A, amount: nat,
)
    ensures state_after_transfer(s, from, to, amount).total_supply == s.total_supply,
{
}

/// (#3) Accounts other than `from` and `to` keep their balances exactly.
pub proof fn lemma_transfer_preserves_other_balances<A>(
    s: State<A>, from: A, to: A, amount: nat,
)
    requires from != to,
    ensures
        forall|k: A| #![auto]
            k != from && k != to ==>
                state_after_transfer(s, from, to, amount).balances[k] == s.balances[k],
{
}

/// (#2) Self-transfer with a positive amount inflates the book-balance by
/// `amount` — explains why `Fungible::transfer` must `require!(sender != receiver)`.
pub proof fn lemma_self_transfer_inflates_sum<A>(
    s: State<A>, who: A, amount: nat,
)
    requires
        s.balances.dom().finite(),
        s.balances.dom().contains(who),
        s.balances[who] + amount <= u128::MAX,
    ensures
        sum_balances(state_after_transfer(s, who, who, amount).balances)
            == sum_balances(s.balances) + amount,
{
    let f = s.balances[who];
    let m1 = s.balances.insert(who, (f - amount) as nat);
    let m2 = m1.insert(who, (f + amount) as nat);

    assert(m2 =~= s.balances.insert(who, (f + amount) as nat));
    lemma_sum_after_insert(s.balances, who, (f + amount) as nat);
}

} // verus!
