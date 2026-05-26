# TODO

Open issues and deferred work, organised by topic.

## Verus / verifier-level

### Sub-message / cross-contract dispatch (large)

CosmWasm contracts return a `Response { messages: Vec<SubMsg>, ... }`. The
host runtime dispatches each `SubMsg` *after* the current call returns;
optionally a `reply` handler fires with the outcome. Other chains have
analogous mechanisms (NEAR `Promise`, Solana CPI, Ethereum `call`/etc.,
Linera cross-microchain messages).

A faithful verification needs to model:

  - the runtime's dispatch loop (sequence of `SubMsg`s),
  - per-`SubMsg` failure semantics (`ReplyOn::{Never, Always, Success, Error}`),
  - the called contract's effect on shared state (worst-case assumption is
    usually the safe move),
  - reentrancy: between our `SubMsg`-issuing return and our `reply` handler
    firing, *any* state changes are possible from other contracts calling
    back into us.

Concretely for cw20: the `Send` variant transfers tokens *and* calls a
receiver-contract callback. This is where production cw20 bugs concentrate.

Effort: 2–4 weeks per chain, plus ongoing maintenance as the chains'
runtime semantics evolve.

Concrete entry point if/when revisited:
- Spec function `dispatch(state, submsg_list) -> state'`.
- Treat the called contract's effect as an uninterpreted relation that
  preserves *our* invariants (modulo what we explicitly export).
- Verify our `reply` handler is correct under any post-dispatch state.

### Verus dyn-trait reborrow limitation

`&mut dyn Trait → &mut dyn Trait` (implicit reborrow) is not supported
in the current Verus. We worked around in CosmWasm by:
  - making `verified_*` helpers generic over `S: Storage` (Sized),
  - wrapping `&mut dyn Storage` in a concrete `StoreRef<'_>` at the entry
    point.

Cost: ~8 lines of wrapper boilerplate per CosmWasm contract. Same shape
will be needed wherever a contract operates on a runtime-provided
trait-object reference (likely IC, Linera, Substrate/ink!).

Upstream fix would be a Verus PR adding unsizing-coercion support for
`&mut dyn T`. Out of scope for now.

### `ToKey: Sealed` blocks generic-hasher axiomatization on NEAR

`near_sdk::store::key::ToKey` has a private super-trait `Sealed` in
`near_sdk::store::key::private`. `external_trait_specification` requires
exact super-trait matching, which we can't do because `Sealed`'s path is
inaccessible. We sidestepped by:
  - wrapping `LookupMap<K, V, Identity>` in our own `AxLookupMap<K, V>`,
  - specialising the wrapper to the default `Identity` hasher.

To support alternate hashers (`Sha256`, `Keccak256`) would need either:
  - a Verus extension allowing private super-traits in
    `external_trait_specification`, or
  - a separate wrapper per hasher.

### Q-generic borrow specialisation in NEAR LookupMap axioms

`LookupMap::{get, contains_key, remove}` are generic over `Q` with
`K: Borrow<Q>`. Our axioms specialise to `Q = K`. The general form
would require `borrows_to_key` / `maps_borrowed_key_to_value` helper
predicates (vstd does this for `BTreeMap`). Not needed for the
fungible-token example; would matter for contracts that look up
`String` keys via `&str`.

### `Fungible::transfer`'s remaining unverified glue (NEAR)

One line:
```rust
verified_transfer(&mut self.balances, receiver, amount);
```

Verifying it requires either:
  - declaring `Fungible` to Verus via `external_type_specification` plus
    field-access axioms, or
  - rewriting the contract without `#[near(contract_state)]` and
    emitting the wasm bindings by hand.

Both are deferred; the line itself is dispatch, no logic.

## Per-chain status

### NEAR

| component | status |
|---|---|
| arithmetic + State conservation | ✅ verified |
| storage refinement (`AxLookupMap`) | ✅ verified |
| caller resolution via axiomatized `predecessor()` | ✅ verified |
| `Fungible::transfer` body | 1 line of unverified glue (see above) |
| cw20-style allowance / mint / burn | not implemented (NEAR fungible standard is FT-160, slightly different) |
| cross-contract `Promise` calls | not modelled |

### CosmWasm

| component | status |
|---|---|
| arithmetic + State conservation | ✅ verified |
| storage refinement (`balances_view` etc.) | ✅ verified |
| caller passed as `info.sender` parameter | trivial (no axiom needed) |
| Entry points (instantiate / execute / query) | ✅ all routed through verified helpers |
| cw20 surface (transfer/approve/transfer_from/mint/burn/inc/dec allowance/update_minter) | ✅ verified |
| State-level connection to `core::state_after_*` | ✅ via refinement lemmas, woven into ensures |
| `Send` variant (callback-bearing transfer) | not implemented (see sub-message section above) |
| IBC | not modelled |

### Solana, Linera, IC, Gear, ink!, MultiversX

Verification work not yet started. Plan: port the NEAR/CosmWasm pattern,
attack chain-specific axiomatization challenges as they arise.

#### Per-chain hard parts we expect

- **Solana**: account model (state in raw byte buffers, not per-instance
  structs); each instruction takes a `&[AccountInfo]` and must validate
  ordering/permissions. Axiomatization is heavier than NEAR/CosmWasm.
- **Linera**: View framework + cross-microchain messages + async by
  default. With a sync SDK variant (user-supplied), View framework
  becomes the main axiomatization work.
- **IC**: `caller()` is env-based (like NEAR), state is in `thread_local!`
  (like NEAR). Should be a relatively straightforward port.
- **Gear**: actor / message-handler model; verifying the handler dispatch
  layer is the work.
- **ink!**: `#[ink::contract]` macro wraps the entire module; factoring
  out a verified core requires careful module organisation.
- **MultiversX**: trait-based contract macro is invasive; types
  (`BigUint`, `ManagedAddress`, `SingleValueMapper`) are framework-bound.

## Infrastructure

### vstd version pinning is awkward

Our Verus repo tracks `release/0.2026.05.17.e479cce` because cargo-published
`vstd = "=0.0.0-2026-05-17-0151"` is tied to that. Drift between repo `main`
and the published vstd breaks builds. Long-term: pin Verus install to a
released tag (we already do this) or use `[patch.crates-io]` to a local
vstd path.

### Build/test runners are per-chain idiosyncratic

`build_all.sh` / `test_all.sh` work but each chain has its own target
override / feature dance:
- NEAR: needs `--target wasm32-unknown-unknown` for build, host triple
  for test (with `unit-testing` dev-feature).
- CosmWasm: defaults work.
- Each new chain will likely add to the matrix.

Could consolidate into per-chain `verify.sh` scripts at some point.
