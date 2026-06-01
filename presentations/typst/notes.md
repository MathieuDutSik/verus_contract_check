# Speaker notes — 25-min Verus / cross-chain verification talk

Target: ~20 minutes of speaking + 5 minutes Q&A.

Audience: engineers with an Ethereum background. They know Solidity, EVM bugs,
Certora, K-framework. They likely don't read Rust fluently. Don't dwell on
syntax; lean on the architecture and the cross-chain angle.

## Slide-by-slide timing

| # | slide | min | what to say (compressed) |
|---|---|---|---|
| 1 | Title | 0.5 | Name, what the talk is. "I'm going to argue that the same proof can cover eight different chains." |
| 2 | The bug | 1.5 | Anchor in Compound's MASTER inflation (Sep 2021, $80M). State the invariant in words. "No test of any size proves this holds for all inputs." |
| 3 | Tests vs. proofs | 1.5 | The asymmetry. Verification searches for counter-examples; testing waits to be handed one. |
| 4 | Verus in one slide | 2.5 | Walk through the `ensures` clause. "This is real production Rust — the same bytes go to the deployer." Don't read all the code; point at `from_next + to_next == from_balance + to_balance`. |
| 5 | The framing question | 1 | "Eight chains. The question is what's portable." Make eye contact here. This is the headline. |
| 6 | Eight chains table | 1.5 | Highlight: Solana has accounts (not maps), MultiversX has unbounded ints, Linera has async messages. Same triple: caller-receiver-amount. |
| 7 | Three-layer architecture | 2 | Walk top-down. "Layer 3 is unverified glue, ~5 lines. Layer 2 has the substantive proofs. Layer 1 is the chain-agnostic conservation theorem. Each layer is the minimum trust surface." |
| 8 | Conservation, once for all chains | 1.5 | The `State<A>` is generic. The lemma is proven once, used eight times. ~15 lines of proof, by induction on the map's domain. |
| 9 | CosmWasm clean case | 1.5 | "This is what done looks like." Full cw20 surface. 11 obligations, 24 tests still pass. |
| 10 | MultiversX BigUint | 1.5 | The interesting part for this audience. BigUint maps to `nat` *without* an overflow precondition — better than `u128`. |
| 11 | The trait-cascade obstacle | 2 | Tell as a problem-solving story. "I tried three forms. The fourth worked." Show the working syntax. Lesson: same fix unblocked Linera. |
| 12 | NEAR Sealed (the wall) | 1.5 | Honest about a limitation. "Privacy in the SDK is invisible to the verifier. There's no workaround at the verifier level." |
| 13 | Numbers | 1.5 | Read the rightmost column. Emphasize zero errors. Mention the shared-crate refactor (440 LOC of duplication eliminated). |
| 14 | Comparison | 1 | One sentence per row. Tradeoff at the bottom: axioms are trust, kept small. |
| 15 | Open problems | 1.5 | Lead with reentrancy — they'll ask anyway. "This is where production-cw20 bugs concentrate. ~2-4 weeks per chain to model." |
| 16 | Lessons | 1.5 | The three crisp takeaways. The middle one (SDK privacy) is the most original — pause there. |
| 17 | Closing | 0.5 | One sentence. Hands to Q&A. |

Total speaking ≈ 22 min. Buffer for transitions/jokes ≈ 1 min. Q&A ≈ 5 min.

## Anticipated questions

**"Why not Certora / K?"** — Different target. K models EVM bytecode operational semantics. Certora is SMT over Solidity. Verus is refinement on production Rust → applies to any chain whose contracts compile through Rust. They're complementary, not competitors.

**"Reentrancy?"** — Open problem (slide 15). Be honest. The architectural shape (uninterpreted relation for the called contract's effect; check our invariants survive any post-state) is known. ~2-4 weeks per chain.

**"What's in the trusted base?"** — Per chain: the `<chain>_axioms.rs` file (~30 lines), the SDK macro expansion, the Borsh/Serde derives, the wasm runtime. Per-shared: `verus_fungible_core` itself (verified) + Verus + Z3 + the Rust→Verus translator. Documented in DESIGN.md.

**"Could this verify a real production token?"** — The shape applies. The pieces missing (cw20 `Send` variant, allowance edge cases, IBC) are listed in TODO.md. Estimated effort to take cw20 to production-grade verification: ~6-8 weeks. Worth doing for a chain that wants to claim "verified token standard."

**"What about ERC-20?"** — We didn't touch EVM. The Rust→wasm pattern doesn't directly cross-compile to EVM. K and Certora are the right tools there. *But* if a chain has an EVM-compatible layer that's also Rust-based (e.g., Substrate's pallet-evm, Solana's Neon), Verus applies.

**"Verus stability / production-readiness?"** — Open-source project, MS Research / academic origin. Active development, breaking changes per release. Pin the toolchain per crate (we pin to `0.0.0-2026-05-17-0151`). Not as battle-tested as Certora; ahead of K in expressiveness.

**"What did you find that you didn't expect?"** — Two things to mention:
1. The Tier-A wiring disconnects — chains where the verified helper existed but the deployed function bypassed it. *The verified obligation was for dead code.* Without auditing the call chain, the proofs would have given false confidence.
2. BigUint is *easier* to verify than u128 conservation. Unbounded types have no overflow caveat; you spec what you mean.

## Notes on delivery

- *Don't* read the slides. They're scaffolding.
- *Do* point at the code: "this `ensures` clause", "this conservation equation."
- The MultiversX trait-cascade story is the live problem-solving demonstration. Tell it with timing — pause after each failed attempt.
- If you're running long, drop slide 14 (comparison) — verbal version is fine.
- If you're running short, expand slide 8 (the conservation lemma) — it's the heart of the work.

## What to *not* say

- Don't bash other tools. Certora and K are good at what they do.
- Don't oversell. We didn't verify cross-contract dispatch; say so.
- Don't lean on Rust syntax explanations. The audience will tune out.
- Don't claim "proof is correctness" — proofs are correctness *relative to the axioms*. The slide-13 numbers are obligations discharged, not bugs eliminated absent the axioms.

## Useful concrete answers if asked

- Total LOC across all eight chains (verified + axioms + glue): ~5,500.
- Time to verify the full project from clean: ~45 seconds.
- Z3 timeout per obligation: default (~30s); none currently hit it.
- Shared core verifies in ~5 seconds (12 obligations).
- Worst-case per-chain verification time: linera_alternate, ~12 seconds (8 local + transitive checks).
