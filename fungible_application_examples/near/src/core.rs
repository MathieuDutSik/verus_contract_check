// Pure fungible-token logic, verified with Verus.
//
// Two layers of guarantee in this module:
//
// 1. `transfer_balances` — exec function on plain u128s.
//    Proves: on success, the two balances sum to the same value as before.
//    This is what `bindings::Fungible::transfer` calls at runtime.
//
// 2. `State` + `state_after_transfer` + `lemma_transfer_preserves_invariant`
//    — spec-level model.
//    Proves: with the invariant `sum_balances(balances) == total_supply`,
//    a transfer between two existing accounts preserves the invariant.
//
// Layer (1) is the executable arithmetic. Layer (2) is the global
// conservation property over an arbitrary number of accounts. The
// glue between the two — that bindings' LookupMap correctly mirrors the
// spec Map — is currently unverified; it's the next layer to attack.

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

pub type AccountId = int;

pub struct State {
    pub total_supply: nat,
    pub balances: Map<AccountId, nat>,
}

/// Recursive sum of all balance values in the map.
pub open spec fn sum_balances(m: Map<AccountId, nat>) -> nat
    decreases m.dom().len() when m.dom().finite()
{
    if m.dom().finite() && m.dom().len() == 0 {
        0nat
    } else {
        let k = m.dom().choose();
        m[k] + sum_balances(m.remove(k))
    }
}

impl State {
    /// Conservation invariant: book-balance equals declared supply,
    /// and the domain is finite (needed for sum to be well-defined).
    pub open spec fn invariant(self) -> bool {
        self.balances.dom().finite()
        && sum_balances(self.balances) == self.total_supply
    }
}

/// New state after `amount` moves from `from` to `to`.
pub open spec fn state_after_transfer(s: State, from: AccountId, to: AccountId, amount: nat) -> State
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
///
/// Proof strategy: induction on the map domain size. Both `sum_balances`
/// calls unfold against the same `choose()` element because their domains
/// are equal (insert at a present key doesn't change the domain).
pub proof fn lemma_sum_after_insert(m: Map<AccountId, nat>, k: AccountId, v_new: nat)
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
        // The chosen element is exactly the updated one. After removing
        // it from both maps, the remainders are identical.
        assert(m2.remove(k) =~= m.remove(k));
        // sum(m)  = m[k]    + sum(m.remove(k))
        // sum(m2) = m2[k]   + sum(m2.remove(k))
        //         = v_new   + sum(m.remove(k))
        // sum(m2) + m[k]   = v_new + sum(m.remove(k)) + m[k]
        //                  = sum(m) + v_new  ✓
    } else {
        // The chosen element is something else; recurse on the smaller
        // map `m.remove(k0)`, where k is still present.
        assert(m.remove(k0).dom().contains(k));
        assert(m.remove(k0)[k] == m[k]);
        lemma_sum_after_insert(m.remove(k0), k, v_new);
        // IH: sum(m.remove(k0).insert(k, v_new)) + m[k]
        //   == sum(m.remove(k0)) + v_new
        //
        // And: m2.remove(k0) == m.remove(k0).insert(k, v_new) because
        // remove/insert commute on distinct keys.
        assert(m2.remove(k0) =~= m.remove(k0).insert(k, v_new));
        // sum(m)  = m[k0] + sum(m.remove(k0))
        // sum(m2) = m[k0] + sum(m2.remove(k0))
        //         = m[k0] + sum(m.remove(k0).insert(k, v_new))
        // sum(m2) + m[k]
        //   = m[k0] + sum(m.remove(k0).insert(k, v_new)) + m[k]
        //   = m[k0] + sum(m.remove(k0)) + v_new        (by IH)
        //   = sum(m) + v_new  ✓
    }
}

/// Main theorem: a transfer between two distinct present accounts
/// preserves the conservation invariant.
pub proof fn lemma_transfer_preserves_invariant(
    s: State,
    from: AccountId,
    to: AccountId,
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

    // Apply the replace-lemma at `from` on the original map.
    lemma_sum_after_insert(m0, from, (f - amount) as nat);
    // sum(m1) + f == sum(m0) + (f - amount)
    // i.e. sum(m1) == sum(m0) - amount

    // Apply the replace-lemma at `to` on m1. We need: `to` is still in m1
    // (true because from != to) and m1[to] == t.
    assert(m1.dom().contains(to));
    assert(m1[to] == t);
    lemma_sum_after_insert(m1, to, (t + amount) as nat);
    // sum(m2) + t == sum(m1) + (t + amount)
    // sum(m2) == sum(m1) + amount == (sum(m0) - amount) + amount == sum(m0)

    assert(m2.dom().finite());
}

// -- Tightening lemmas (#2, #3, #4) -------------------------------------

/// (#4) The supply field is invariant under transfer — trivial because
/// `state_after_transfer` constructs the new state with `total_supply:
/// s.total_supply` verbatim.
pub proof fn lemma_transfer_preserves_total_supply(
    s: State, from: AccountId, to: AccountId, amount: nat,
)
    ensures state_after_transfer(s, from, to, amount).total_supply == s.total_supply,
{
}

/// (#3) Accounts other than `from` and `to` keep their balances exactly.
/// Follows directly from `Map::insert`'s point-modification axiom.
pub proof fn lemma_transfer_preserves_other_balances(
    s: State, from: AccountId, to: AccountId, amount: nat,
)
    requires from != to,
    ensures
        forall|k: AccountId| #![auto]
            k != from && k != to ==>
                state_after_transfer(s, from, to, amount).balances[k] == s.balances[k],
{
}

/// (#2) Self-transfer with a positive amount inflates the book-balance by
/// `amount` — the second `insert(who, t + amount)` overrides the first
/// `insert(who, f - amount)`, and since `f == t`, the net effect is
/// `s.balances.insert(who, f + amount)`. This is why `Fungible::transfer`
/// must `require!(sender != receiver)`.
pub proof fn lemma_self_transfer_inflates_sum(
    s: State, who: AccountId, amount: nat,
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

    // The second insert at the same key overrides the first.
    assert(m2 =~= s.balances.insert(who, (f + amount) as nat));

    // sum(s.balances.insert(who, f+amount)) + s.balances[who]
    //   == sum(s.balances) + (f + amount)
    // i.e. sum(m2) + f == sum(s.balances) + f + amount
    // i.e. sum(m2)     == sum(s.balances) + amount  ✓
    lemma_sum_after_insert(s.balances, who, (f + amount) as nat);
}

} // verus!
