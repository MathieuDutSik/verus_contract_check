// Chain-agnostic verified fungible-token core. Shared by all per-chain crates.
//
// Three concerns live here:
//
//   1. Executable arithmetic on u128 (`transfer_balances`).
//      Plain Rust that the contract calls at runtime; the `ensures` clause
//      pins down conservation of (from + to) and the per-account deltas.
//
//   2. The spec-level `State<A>` and its conservation invariant
//      `sum_balances(balances) == total_supply`, plus state-after-* and
//      the preservation lemmas for transfer, mint, and burn.
//
//   3. Generic storage spec helpers that every chain's verified storage
//      layer needs: `balance_at`, `transfer_balances_map`, `nat_balances`,
//      and the refinement lemma `lemma_balance_map_transfer_matches_state`.
//      These used to live duplicated per-chain.
//
// The type parameter `A` is the account-identifier type (Addr / AccountId /
// Principal / ActorId / Pubkey / AccountOwner / ManagedAddress / …). Per-chain
// crates instantiate `A` to their own opaque address type.
//
// `#![no_std]` so Gear (a no_std chain) can consume this. Nothing here uses
// the std prelude — only spec types from `vstd`.

#![cfg_attr(not(test), no_std)]

use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::map::*;

verus! {

// =====================================================================
// Layer 1 — executable transfer arithmetic
// =====================================================================

pub fn transfer_balances(
    from_balance: u128,
    to_balance: u128,
    amount: u128,
) -> (r: Result<(u128, u128), &'static str>)
    ensures
        match r {
            Ok((from_next, to_next)) =>
                from_next + to_next == from_balance + to_balance
                && from_next == from_balance - amount
                && to_next == to_balance + amount,
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

// =====================================================================
// Layer 2 — spec-level State and conservation lemmas
// =====================================================================

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
    assert(m2.dom() =~= m.dom());

    let k0 = m.dom().choose();
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

/// The supply field is invariant under transfer.
pub proof fn lemma_transfer_preserves_total_supply<A>(
    s: State<A>, from: A, to: A, amount: nat,
)
    ensures state_after_transfer(s, from, to, amount).total_supply == s.total_supply,
{
}

/// Accounts other than `from` and `to` keep their balances exactly.
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

/// Self-transfer with a positive amount inflates the book-balance by
/// `amount` — explains why every chain's `transfer` must reject self-transfer.
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

// ---- Mint & burn ----------------------------------------------------
//
// Mint and burn change `total_supply`. The invariant
// `sum(balances) == total_supply` is preserved because the supply change
// and the balance change are equal.

/// New state after minting `amount` to `to`.
pub open spec fn state_after_mint<A>(s: State<A>, to: A, amount: nat) -> State<A>
    recommends
        s.balances.dom().contains(to),
{
    let t = s.balances[to];
    State {
        total_supply: s.total_supply + amount,
        balances:     s.balances.insert(to, (t + amount) as nat),
    }
}

/// New state after burning `amount` from `from`.
pub open spec fn state_after_burn<A>(s: State<A>, from: A, amount: nat) -> State<A>
    recommends
        s.balances.dom().contains(from),
        s.balances[from] >= amount,
{
    let f = s.balances[from];
    State {
        total_supply: (s.total_supply - amount) as nat,
        balances:     s.balances.insert(from, (f - amount) as nat),
    }
}

/// Mint preserves the conservation invariant: `total_supply` and
/// `sum(balances)` grow by the same amount.
pub proof fn lemma_mint_preserves_invariant<A>(s: State<A>, to: A, amount: nat)
    requires
        s.invariant(),
        s.balances.dom().contains(to),
    ensures
        state_after_mint(s, to, amount).invariant(),
{
    let t = s.balances[to];
    lemma_sum_after_insert(s.balances, to, (t + amount) as nat);
}

/// Burn preserves the conservation invariant: both sides decrease by `amount`.
pub proof fn lemma_burn_preserves_invariant<A>(s: State<A>, from: A, amount: nat)
    requires
        s.invariant(),
        s.balances.dom().contains(from),
        s.balances[from] >= amount,
        s.total_supply >= amount,
    ensures
        state_after_burn(s, from, amount).invariant(),
{
    let f = s.balances[from];
    lemma_sum_after_insert(s.balances, from, (f - amount) as nat);
}

// =====================================================================
// Layer 2.5 — generic storage spec helpers
// =====================================================================
//
// These used to live duplicated in each per-chain lib.rs. They are
// parametric in the address type `A` so each chain re-uses them by
// passing its own address type (Addr / AccountId / Principal / ActorId
// / Pubkey / AccountOwner / ManagedAddress).

/// Balance of `k` in `m`, with absent entries treated as 0.
pub open spec fn balance_at<A>(m: Map<A, u128>, k: A) -> u128 {
    if m.dom().contains(k) { m[k] } else { 0u128 }
}

/// The balance map after a transfer of `amount` from `sender` to `receiver`.
/// Matches `state_after_transfer`'s balance update at the `u128` level.
pub open spec fn transfer_balances_map<A>(
    m: Map<A, u128>,
    sender: A,
    receiver: A,
    amount: u128,
) -> Map<A, u128> {
    m.insert(sender,   (balance_at(m, sender) - amount) as u128)
     .insert(receiver, (balance_at(m, receiver) + amount) as u128)
}

/// Lift a `u128`-valued balance map into the `nat`-valued spec map used
/// by `State<A>`. Bridges Layer 1 (`u128` storage) and Layer 2 (`nat` spec).
pub open spec fn nat_balances<A>(m: Map<A, u128>) -> Map<A, nat> {
    Map::new(
        |a: A| m.dom().contains(a),
        |a: A| m[a] as nat,
    )
}

/// Refinement: the `u128`-level transfer matches the `nat`-level transfer
/// (`state_after_transfer`'s balance field) under `nat_balances`, provided
/// the arithmetic doesn't under/overflow.
pub proof fn lemma_balance_map_transfer_matches_state<A>(
    balances_pre: Map<A, u128>,
    sender:       A,
    receiver:     A,
    amount:       u128,
)
    requires
        sender != receiver,
        balances_pre.dom().contains(sender),
        balances_pre.dom().contains(receiver),
        balances_pre[sender] >= amount,
        balances_pre[receiver] as int + amount as int <= u128::MAX as int,
    ensures
        nat_balances(transfer_balances_map(balances_pre, sender, receiver, amount))
            == state_after_transfer(
                State {
                    total_supply: 0nat,
                    balances:     nat_balances(balances_pre),
                },
                sender, receiver, amount as nat,
            ).balances,
{
    let bp  = balances_pre;
    let f   = bp[sender];
    let t   = bp[receiver];
    let lhs = nat_balances(
        bp.insert(sender,   (f - amount) as u128)
          .insert(receiver, (t + amount) as u128)
    );
    let rhs = state_after_transfer(
        State {
            total_supply: 0nat,
            balances:     nat_balances(bp),
        },
        sender, receiver, amount as nat,
    ).balances;

    assert(lhs.dom() =~= rhs.dom());

    assert forall|k: A| #[trigger] lhs.dom().contains(k)
        implies lhs[k] == rhs[k]
    by {
        if k == sender {
            // Both reduce to (f - amount) as nat by the precondition f >= amount.
        } else if k == receiver {
            // Both reduce to (t + amount) as nat by the overflow precondition.
        } else {
            assert(bp.dom().contains(k));
        }
    }
    assert(lhs =~= rhs);
}

/// Refinement: the `u128`-level mint update matches `state_after_mint`'s
/// balance field under `nat_balances`, provided the arithmetic doesn't overflow.
pub proof fn lemma_balance_map_mint_matches_state<A>(
    balances_pre: Map<A, u128>,
    supply_pre:   u128,
    to:           A,
    amount:       u128,
)
    requires
        balances_pre.dom().contains(to),
        balances_pre[to] as int + amount as int <= u128::MAX as int,
        supply_pre as int + amount as int <= u128::MAX as int,
    ensures
        nat_balances(balances_pre.insert(to, (balances_pre[to] + amount) as u128))
            == state_after_mint(
                State {
                    total_supply: supply_pre as nat,
                    balances:     nat_balances(balances_pre),
                },
                to, amount as nat,
            ).balances,
{
    let bp  = balances_pre;
    let t   = bp[to];
    let lhs = nat_balances(bp.insert(to, (t + amount) as u128));
    let rhs = state_after_mint(
        State {
            total_supply: supply_pre as nat,
            balances:     nat_balances(bp),
        },
        to, amount as nat,
    ).balances;

    assert(lhs.dom() =~= rhs.dom());

    assert forall|k: A| #[trigger] lhs.dom().contains(k)
        implies lhs[k] == rhs[k]
    by {
        if k == to {
        } else {
            assert(bp.dom().contains(k));
        }
    }
    assert(lhs =~= rhs);
}

/// Refinement: the `u128`-level burn update matches `state_after_burn`'s
/// balance field under `nat_balances`.
pub proof fn lemma_balance_map_burn_matches_state<A>(
    balances_pre: Map<A, u128>,
    supply_pre:   u128,
    from:         A,
    amount:       u128,
)
    requires
        balances_pre.dom().contains(from),
        balances_pre[from] >= amount,
        supply_pre >= amount,
    ensures
        nat_balances(balances_pre.insert(from, (balances_pre[from] - amount) as u128))
            == state_after_burn(
                State {
                    total_supply: supply_pre as nat,
                    balances:     nat_balances(balances_pre),
                },
                from, amount as nat,
            ).balances,
{
    let bp  = balances_pre;
    let f   = bp[from];
    let lhs = nat_balances(bp.insert(from, (f - amount) as u128));
    let rhs = state_after_burn(
        State {
            total_supply: supply_pre as nat,
            balances:     nat_balances(bp),
        },
        from, amount as nat,
    ).balances;

    assert(lhs.dom() =~= rhs.dom());

    assert forall|k: A| #[trigger] lhs.dom().contains(k)
        implies lhs[k] == rhs[k]
    by {
        if k == from {
        } else {
            assert(bp.dom().contains(k));
        }
    }
    assert(lhs =~= rhs);
}

// =====================================================================
// Shared TransferError
// =====================================================================
//
// Union of every variant any chain raises. Chains construct only the
// variants they need; the others remain unconstructed. Defined inside
// `verus!{}` so verified code can return/match on it.

#[derive(PartialEq, Eq, Debug)]
pub enum TransferError {
    SelfTransfer,
    Insufficient,
    Overflow,
    InsufficientAllowance,
    InsufficientSupply,
    Unauthorized,
}

} // verus!
