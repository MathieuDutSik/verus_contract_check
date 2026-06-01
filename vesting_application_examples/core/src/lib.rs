// Chain-agnostic verified linear-vesting core. Shared by all per-chain
// vesting crates.
//
// Three concerns live here, mirroring the layout of the fungible core:
//
//   1. Executable arithmetic on u128 (`compute_vested`, `compute_claim`).
//      Ordinary checked-arithmetic Rust the contract calls at runtime;
//      `ensures` clauses connect the runtime value to the spec-level
//      `vested_at` / `claimable_at`.
//
//   2. The spec-level `State<A>` and its invariant
//      `claimed <= total`, plus state-after-claim and the preservation
//      and monotonicity lemmas.
//
//   3. The vesting schedule itself: a spec-level pure function
//      `vested_at(p, t) -> nat` returning how much *should* be released
//      at wall-clock time `t`, with:
//
//        - cliff:     t  <  start + cliff_duration       => 0
//        - complete:  t  >= start + vest_duration         => total
//        - linear:    otherwise: total * (t - start) / vest_duration
//
//      And theorems:
//
//        bounded:     vested_at(p, t)  <=  p.total
//        monotonic:   t1 <= t2  ==>  vested_at(p, t1) <= vested_at(p, t2)
//        cliff_zero:  t < start + cliff_duration  ==>  vested_at(p, t) == 0
//        complete:    t >= start + vest_duration  ==>  vested_at(p, t) == total
//
// The type parameter `A` is the beneficiary-identifier type (AccountId
// on NEAR, Addr on CosmWasm, Principal on IC, etc.). Per-chain crates
// instantiate `A` to their own opaque address type.
//
// `#![no_std]` so no_std chains can consume this. Nothing here uses the
// std prelude — only spec types from `vstd`.

#![cfg_attr(not(test), no_std)]

use vstd::prelude::*;

verus! {

// =====================================================================
// Layer 0 — schedule parameters
// =====================================================================
//
// All four fields are public. `well_formed` rules out the degenerate
// shapes (zero-duration vest, cliff longer than the vest itself) so the
// linear branch's denominator is non-zero and `vested_at` is monotonic
// in `t` across the whole timeline.

pub struct Params {
    /// Wall-clock time the grant begins. The beneficiary may have
    /// nothing claimable until `start + cliff_duration`.
    pub start: u64,
    /// How long after `start` before *anything* vests. May be 0.
    pub cliff_duration: u64,
    /// Total length of the vest, measured from `start`. At
    /// `start + vest_duration` the full `total` is released.
    pub vest_duration: u64,
    /// The total grant size. Across the whole timeline the released
    /// amount is bounded above by this value.
    pub total: u128,
}

impl Params {
    /// Well-formedness:
    ///   - the vest has positive length (denominator non-zero),
    ///   - the cliff doesn't extend past the vest's end.
    /// Both are needed for `vested_at` to be a sensible schedule.
    pub open spec fn well_formed(self) -> bool {
        self.vest_duration > 0
        && self.cliff_duration <= self.vest_duration
    }
}

// =====================================================================
// Layer 1 — the vesting schedule (spec-level)
// =====================================================================

/// How much *should* be released at wall-clock time `t`, regardless of
/// how much the beneficiary has actually claimed so far. This is the
/// pure schedule; the contract's `claim()` reconciles it against
/// `state.claimed`.
///
/// Three branches:
///   - Before the cliff: nothing vested.
///   - After the full vest: everything vested.
///   - In between: linear interpolation `total * elapsed / vest_duration`.
///
/// All arithmetic is done at `int` then cast back to `nat`, so the
/// `u64 + u64` sums that appear in the conditions never wrap.
pub open spec fn vested_at(p: Params, t: u64) -> nat
{
    if (t as int) < (p.start as int) + (p.cliff_duration as int) {
        0nat
    } else if (t as int) >= (p.start as int) + (p.vest_duration as int) {
        p.total as nat
    } else {
        let elapsed: nat = ((t as int) - (p.start as int)) as nat;
        ((p.total as nat) * elapsed) / (p.vest_duration as nat)
    }
}

// ---- Schedule theorems ----------------------------------------------

/// Bounded above: the schedule never releases more than the grant total.
/// In the linear branch this needs the fact that `elapsed <= vest_duration`
/// and that integer division `(a*b) / b == a` when `b > 0`.
pub proof fn lemma_vested_bounded(p: Params, t: u64)
    requires p.well_formed(),
    ensures  vested_at(p, t) <= p.total as nat,
{
    let total_n = p.total as nat;
    let vest_n  = p.vest_duration as nat;

    if (t as int) < (p.start as int) + (p.cliff_duration as int) {
        // cliff branch: 0 <= total
    } else if (t as int) >= (p.start as int) + (p.vest_duration as int) {
        // complete branch: total <= total
    } else {
        let elapsed: nat = ((t as int) - (p.start as int)) as nat;
        // We're in the linear branch, so t < start + vest_duration,
        // hence elapsed < vest_duration.
        assert(elapsed < vest_n);
        // total * elapsed <= total * vest_duration  (mul monotonic in nat)
        // so the quotient `(total * elapsed) / vest_duration` is at most
        // `(total * vest_duration) / vest_duration == total`.
        assert(total_n * elapsed <= total_n * vest_n) by(nonlinear_arith)
            requires elapsed < vest_n;
        // Z3 can finish from here: division-by-vest_n is monotone in the
        // numerator, and (total*vest)/vest == total.
        assert((total_n * elapsed) / vest_n <= (total_n * vest_n) / vest_n) by(nonlinear_arith)
            requires
                vest_n > 0,
                total_n * elapsed <= total_n * vest_n;
        assert((total_n * vest_n) / vest_n == total_n) by(nonlinear_arith)
            requires vest_n > 0;
    }
}

/// Monotonic in time: more time elapsed ==> at least as much vested.
/// Case-split on which branch each of `t1` and `t2` falls into. The
/// hard case is "both in the linear branch": numerator grows with
/// `elapsed`, and integer division is monotone in the numerator.
pub proof fn lemma_vested_monotonic(p: Params, t1: u64, t2: u64)
    requires
        p.well_formed(),
        t1 <= t2,
    ensures
        vested_at(p, t1) <= vested_at(p, t2),
{
    let total_n = p.total as nat;
    let vest_n  = p.vest_duration as nat;

    let cliff_end: int = (p.start as int) + (p.cliff_duration as int);
    let vest_end:  int = (p.start as int) + (p.vest_duration as int);

    if (t1 as int) < cliff_end {
        // vested_at(p, t1) == 0; anything >= 0 satisfies the goal.
        lemma_vested_bounded(p, t2);
        // 0 <= vested_at(p, t2): vested_at is a nat, trivially.
    } else if (t2 as int) >= vest_end {
        // vested_at(p, t2) == total; bounded lemma closes it.
        lemma_vested_bounded(p, t1);
    } else {
        // Both in the linear branch: t1, t2 in [cliff_end, vest_end).
        // Show the elapsed values are ordered, then numerator-monotonicity
        // of integer division.
        let e1: nat = ((t1 as int) - (p.start as int)) as nat;
        let e2: nat = ((t2 as int) - (p.start as int)) as nat;
        assert(e1 <= e2);

        // total * e1 <= total * e2  (nat multiplication monotone).
        assert(total_n * e1 <= total_n * e2) by(nonlinear_arith)
            requires e1 <= e2;
        // Division by a positive nat is monotone in the numerator.
        assert((total_n * e1) / vest_n <= (total_n * e2) / vest_n)
            by(nonlinear_arith)
            requires
                vest_n > 0,
                total_n * e1 <= total_n * e2;
    }
}

/// Before the cliff, nothing is vested. (Trivial — by definition of the
/// schedule's first branch — but useful as a callable lemma.)
pub proof fn lemma_vested_pre_cliff(p: Params, t: u64)
    requires (t as int) < (p.start as int) + (p.cliff_duration as int),
    ensures  vested_at(p, t) == 0nat,
{
}

/// After the full vest, everything is vested. Requires `well_formed`
/// so the cliff branch can't shadow the complete branch (the spec
/// checks the cliff first).
pub proof fn lemma_vested_complete(p: Params, t: u64)
    requires
        p.well_formed(),
        (t as int) >= (p.start as int) + (p.vest_duration as int),
    ensures  vested_at(p, t) == p.total as nat,
{
}

// =====================================================================
// Layer 2 — State and conservation
// =====================================================================

/// Vesting contract state. One beneficiary, one grant.
#[verifier::reject_recursive_types(A)]
pub struct State<A> {
    pub beneficiary: A,
    pub params:      Params,
    /// How much the beneficiary has already withdrawn. Monotonically
    /// non-decreasing across the contract's lifetime.
    pub claimed:     u128,
}

impl<A> State<A> {
    /// The conservation invariant: claimed is at most the grant total,
    /// and the schedule itself is well-formed.
    pub open spec fn invariant(self) -> bool {
        self.params.well_formed()
        && (self.claimed as nat) <= (self.params.total as nat)
    }
}

/// How much the beneficiary is allowed to withdraw at time `t`:
/// the schedule's `vested_at(t)` minus what they've already claimed.
/// Clamped at 0 in case `claimed` somehow exceeds `vested_at(t)` (which
/// cannot happen if the invariant is preserved — see lemmas below).
pub open spec fn claimable_at<A>(s: State<A>, t: u64) -> nat {
    let v = vested_at(s.params, t);
    let c = s.claimed as nat;
    if v >= c { (v - c) as nat } else { 0nat }
}

/// State after the beneficiary claims everything currently claimable at
/// time `t`. If nothing is claimable (pre-cliff, or already caught up),
/// the state is unchanged. Otherwise `claimed` is bumped to exactly
/// `vested_at(t)`.
pub open spec fn state_after_claim<A>(s: State<A>, t: u64) -> State<A> {
    let v = vested_at(s.params, t);
    let c = s.claimed as nat;
    if v > c {
        State {
            beneficiary: s.beneficiary,
            params:      s.params,
            claimed:     v as u128,
        }
    } else {
        s
    }
}

// ---- Conservation / monotonicity lemmas -----------------------------

/// A claim preserves the invariant: `claimed` only grows, and is still
/// bounded by `total` because `vested_at(p, t) <= total`.
pub proof fn lemma_claim_preserves_invariant<A>(s: State<A>, t: u64)
    requires s.invariant(),
    ensures  state_after_claim(s, t).invariant(),
{
    let v = vested_at(s.params, t);
    let c = s.claimed as nat;
    if v > c {
        // New claimed == v; need v <= total.
        lemma_vested_bounded(s.params, t);
    } else {
        // State unchanged.
    }
}

/// `claimed` is monotone across a single claim. Requires the
/// invariant so we can call `lemma_vested_bounded` and conclude `v as
/// u128` fits — without that, the cast in `state_after_claim` could
/// truncate.
pub proof fn lemma_claim_monotone_in_state<A>(s: State<A>, t: u64)
    requires s.invariant(),
    ensures
        state_after_claim(s, t).claimed >= s.claimed,
{
    let v = vested_at(s.params, t);
    let c = s.claimed as nat;
    if v > c {
        // v <= total <= u128::MAX, so the `as u128` cast inside
        // `state_after_claim` is faithful, and the post-claimed
        // (== v as u128) exceeds the pre-claimed (== c as u128).
        lemma_vested_bounded(s.params, t);
    } else {
        // State unchanged.
    }
}

/// `claimed` is monotone across time, for the same starting state.
/// More wall-clock time ==> at least as much will have been claimed
/// (if the beneficiary actually performs the claim at that time).
pub proof fn lemma_claim_monotone_in_time<A>(s: State<A>, t1: u64, t2: u64)
    requires
        s.invariant(),
        t1 <= t2,
    ensures
        state_after_claim(s, t1).claimed <= state_after_claim(s, t2).claimed,
{
    lemma_vested_monotonic(s.params, t1, t2);
    lemma_vested_bounded(s.params, t1);
    lemma_vested_bounded(s.params, t2);

    let v1 = vested_at(s.params, t1);
    let v2 = vested_at(s.params, t2);
    let c  = s.claimed as nat;

    // Four cases on (v1 > c, v2 > c). v1 <= v2 by monotonicity, so the
    // (v1>c, v2<=c) case can't arise; the others are direct.
    if v1 > c {
        assert(v2 >= v1);
    } else if v2 > c {
        // post1 unchanged at c; post2 jumped to v2 >= c.
    } else {
        // Both unchanged at c.
    }
}

/// Claiming twice at the same time gives the same end state as claiming
/// once. Useful: the contract's `claim` is idempotent in a given block.
pub proof fn lemma_claim_idempotent<A>(s: State<A>, t: u64)
    requires s.invariant(),
    ensures
        state_after_claim(state_after_claim(s, t), t) == state_after_claim(s, t),
{
    let v = vested_at(s.params, t);
    let c = s.claimed as nat;
    if v > c {
        // After one claim, claimed == v; vested_at unchanged at v, so
        // the "v > new_claimed" check fails: state stays put.
        lemma_vested_bounded(s.params, t);
    } else {
        // No-op then no-op.
    }
}

/// Claim is local to the contract's grant total — the parameters are
/// never modified. Trivial but a nice public theorem.
pub proof fn lemma_claim_preserves_params<A>(s: State<A>, t: u64)
    ensures
        state_after_claim(s, t).params      == s.params,
        state_after_claim(s, t).beneficiary == s.beneficiary,
{
}

/// After a claim at time `t`, `claimed == vested_at(t)` (provided we
/// actually moved). So `claimable_at(post, t) == 0`.
pub proof fn lemma_claim_drains_at_time<A>(s: State<A>, t: u64)
    requires s.invariant(),
    ensures
        claimable_at(state_after_claim(s, t), t) == 0nat,
{
    let v = vested_at(s.params, t);
    let c = s.claimed as nat;
    if v > c {
        // post.claimed == v; claimable_at(post, t) = v - v = 0.
        lemma_vested_bounded(s.params, t);
    } else {
        // post == s; claimable_at(s, t) was already 0 (v <= c).
    }
}

// =====================================================================
// Layer 1.5 — executable arithmetic
// =====================================================================
//
// These are the u128/u64 functions the contract actually calls at
// runtime. Each has an `ensures` connecting it to the spec.

/// Compute `vested_at(p, t)` as a u128. Returns Err on a (genuinely
/// astronomical) overflow inside the linear branch; on the cliff /
/// complete branches the value is trivially bounded by `p.total` and
/// always fits.
///
/// The bounded lemma proves the value, *as a nat*, is at most
/// `p.total`. The Err path is reserved for the intermediate product
/// `total * elapsed` exceeding `u128::MAX`. For realistic grants this
/// never fires; we surface it as an honest result rather than silently
/// wrapping.
pub fn compute_vested(p: &Params, t: u64) -> (r: Result<u128, &'static str>)
    requires p.well_formed(),
    ensures
        match r {
            Ok(v)  => v as nat == vested_at(*p, t),
            Err(_) => true,
        },
{
    // The exec form has to be expressed without `start + cliff_duration`
    // or `start + vest_duration` — those u64 sums can overflow. Rewriting
    // as `(t - start) <vs> duration` (after guarding t >= start) is
    // equivalent to the spec's `int`-arithmetic branches for any
    // (t, start, duration) in the u64 range.
    if t < p.start {
        // Pre-start: definitely pre-cliff (cliff_duration >= 0).
        return Ok(0);
    }
    let elapsed_u64: u64 = t - p.start;
    if elapsed_u64 < p.cliff_duration {
        return Ok(0);
    }
    if elapsed_u64 >= p.vest_duration {
        return Ok(p.total);
    }
    // Linear branch. `total * elapsed` could exceed u128::MAX for a
    // genuinely astronomical grant; surface that as Err rather than wrap.
    match p.total.checked_mul(elapsed_u64 as u128) {
        None    => Err("vested-arith-overflow"),
        Some(n) => {
            let q = n / (p.vest_duration as u128);
            Ok(q)
        }
    }
}

/// Compute the claimable amount at time `t` given a pre-claim
/// `claimed` snapshot. Wraps `compute_vested` and subtracts.
///
/// Returns Err on the same astronomical-overflow path as
/// `compute_vested`. Returns Ok(0) in the legitimate "already caught
/// up" case.
pub fn compute_claim(p: &Params, t: u64, claimed: u128) -> (r: Result<u128, &'static str>)
    requires
        p.well_formed(),
        (claimed as nat) <= (p.total as nat),
    ensures
        match r {
            Ok(amount) => {
                amount as nat == claimable_at(
                    State::<()> { beneficiary: (), params: *p, claimed },
                    t,
                )
            }
            Err(_) => true,
        },
{
    match compute_vested(p, t) {
        Err(e)        => Err(e),
        Ok(v) => {
            // v as nat == vested_at(p, t).
            // claimed <= total and v <= total ==> v as u128 vs claimed
            // are both safe. Two cases on the order:
            if v >= claimed {
                Ok(v - claimed)
            } else {
                Ok(0)
            }
        }
    }
}

} // verus!
