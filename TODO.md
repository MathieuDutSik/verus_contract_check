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

### IC

| component | status |
|---|---|
| arithmetic + State conservation | ✅ verified |
| storage wrappers (`read_balance`/`save_balance` over BTreeMap) | ✅ verified |
| caller resolution via axiomatized `caller()` | ✅ verified |
| cw20 surface (transfer/approve/transfer_from/mint/burn/inc/dec/update_minter) | ✅ verified |
| State-level refinement to `core::state_after_*` | not done (could be added; mechanical) |
| Inter-canister calls (Promise-equivalent) | not modelled |

### Gear

| component | status |
|---|---|
| arithmetic + State conservation | ✅ verified |
| storage wrapper (`AxHashMap`) | ✅ verified |
| caller resolution via axiomatized `msg::source()` | ✅ verified |
| `verified_transfer` | ✅ verified |
| `extern "C" fn handle()` dispatch | unverified (touches `static mut`, `msg::*`) |
| cw20 surface | not implemented |

### ink!

| component | status |
|---|---|
| arithmetic + State conservation | ✅ verified |
| arithmetic helpers used by contract (transfer, mint, burn) | ✅ verified |
| storage refinement on `ink::storage::Mapping` | **not done** — see Mapping gap below |
| caller resolution via `Self::env().caller()` | not axiomatized |
| `Self::env().emit_event(...)` | not modelled |

#### Mapping refinement gap on ink!

`ink::storage::Mapping<K, V, KT>` has three trait bounds: `K: Storable`,
`V: Storable`, `KT: StorageKey`. Each is an ink-specific trait with its
own methods (`encode`, `decode`, `encoded_size`, plus dependent
`scale::Encode`/`Decode`/etc.). Axiomatizing the chain involves writing
external_trait_specifications for all of them.

Also, when used inside `#[ink(storage)]`, the macro assigns `KT = AutoKey`
which Verus can't directly reason about; a wrapper would need `ManualKey<K>`
with the same hash the macro would compute.

Effort to fill: 1–2 weeks. Approach: wrap `Mapping` in `AxInkMapping`
(parallel to NEAR's `AxLookupMap`), add `external_trait_specification`
for `Storable` / `StorageKey`, port the storage axioms over.

### MultiversX

| component | status |
|---|---|
| arithmetic + State conservation | ✅ verified |
| contract logic (uses `BigUint`/`ManagedAddress`/`SingleValueMapper`) | **unverified** — see BigUint gap below |
| caller resolution via `self.blockchain().get_caller()` | not axiomatized |

#### BigUint vs `u128` impedance on MultiversX

`multiversx_sc::types::BigUint` is **unbounded** (heap-allocated
arbitrary-precision integer). Our verified `core::transfer_balances`
takes `u128`. So:

- A naive bridge "convert `BigUint` to `u128`" can silently lose data
  for amounts beyond `u128::MAX`. Not acceptable for a token contract.
- The honest fix is to either: (a) axiomatize `BigUint` arithmetic as
  spec-level unbounded `int`/`nat` operations; or (b) duplicate
  `core::transfer_balances` to operate on `BigUint` rather than `u128`.

Effort to fill: substantial. `BigUint` has a large surface
(`+`/`-`/`*`/`/`, comparisons, conversions, encoding) and lives behind
the framework's "managed types" indirection. We'd need
`external_trait_specification` for managed buffers, plus a Verus-aware
arithmetic model that matches the runtime's behaviour.

In the meantime: MultiversX's chain-agnostic `core.rs` does verify
(7 obligations), and the lemmas about `State<A>` are available — they
just aren't connected to the actual contract's BigUint arithmetic.

#### Dependency-version surprise (proc-macro2 conflict)

`multiversx-sc 0.54` pinned `proc-macro2 = "=1.0.86"` exactly, which
collides with `verus_syn`'s `^1.0.101`. Bumping to `multiversx-sc 0.66`
relaxed the pin and resolved it. Lesson: pre-pre-1.0 SDK versions
sometimes have tight transitive pins that conflict with Verus's own
proc-macro stack; using a recent SDK release usually fixes it.

#### Module-name shadowing surprise

`pub mod core;` inside a `#[multiversx_sc::contract]` module shadows
the standard `::core` library that the macro expansion uses
(`::core::mem`). Workaround: rename the module — we used
`#[path = "core.rs"] pub mod fungible_core;`. Same shadowing problem
will recur on any chain whose macros reference `::core` paths and
where we name our verified module `core`.

### Linera

Two variants live side-by-side:

- `fungible_application_examples/linera/` — classic async SDK. **Not
  verified.** The `async`/`await` View API (`MapView::insert(...).await`)
  is the main blocker; Verus has no spec model for async storage handles.
  The microchain message model is the harder semantic piece — see
  "Sub-message" section above.

- `fungible_application_examples/linera_alternate/` — uses the user's
  sync SDK variant
  (`MathieuDutSik/linera-protocol_second` branch
  `alternate_sync_keyvaluestore`, exposing `SyncMapView` /
  `SyncViewStorageContext` / `SyncRootView`). **Shallow port: 15
  verified, 0 errors.**

| component | status |
|---|---|
| chain-agnostic `core::State<A>` (transfer + mint + burn + conservation lemmas) | ✅ 9 obligations |
| `verified_helpers.rs` (allowance/transfer_from u128 kernels matching `state.rs`) | ✅ 6 obligations |
| `Amount` external type spec | not done |
| `SyncMapView<K,V>` external type spec + read/write axioms | not done |
| State-layer integration (lifting kernel proofs to `FungibleTokenState::credit`, `debit`, `approve`, `debit_for_transfer_from`) | not done |
| Cross-microchain `Message::Credit` / `Message::Withdraw` semantics | not done — sub-message blocker |

What today's 15 obligations buy us:
- The arithmetic kernels that `state.rs` reduces to (after stripping
  `Amount` and `SyncMapView`) are proven: no underflow on debit, no
  overflow on credit, allowance correctly decremented in `transfer_from`,
  and (from `core.rs`) `from + to` is conserved across a transfer.
- Same "shallow port" tier as ink!/MultiversX. Linera_alternate is the
  best-positioned chain for *deeper* verification because the sync API
  removes the async-storage blocker entirely.

Path to lifting to the full state-layer:
1. Add `external_type_specification` wrappers for `Amount` (u128
   newtype) and `OwnerSpender`.
2. Axiomatize `SyncMapView<K,V>` via a ghost-view function projecting
   it to `vstd::map::Map<K,V>`, plus `assume_specification` on
   `get`/`insert`/`remove`/`get_mut_or_default`.
3. Re-state `state.rs` methods with `ensures` that connect to the
   `core::State<A>` invariants — should be mechanical once (1)+(2)
   land.

### Solana

| component | status |
|---|---|
| arithmetic + allowance + mint/burn at `apply_*` layer | ✅ verified (16 obligations) |
| `AccountInfo` external type + ghost views (`ai_signed`, `ai_key`, `ai_token_data`, `ai_mint_data`) | ✅ axiomatized |
| Borsh round-trip wrapped via `read_*`/`write_*_data` axioms | ✅ axiomatized (trusted) |
| `verified_transfer_instruction` — dispatch-level verification | ✅ partial (see below) |
| Other 6 instructions wrapped with `verified_*_instruction` | not done; replicate `transfer`'s pattern |
| Framing layer over `ai_token_data` (writeback effect on other accounts) | **not done** — Verus's pure-function model can't track this without explicit state |
| PDA verification | skipped (not needed for self-contained fungible token) |
| CPI modeling | skipped (no outbound CPI in this contract) |
| Rent | skipped (apply-layer preconditions only) |

#### What `verified_transfer_instruction` does and doesn't guarantee

What we get today:
- Verus rejects any version that doesn't `read_is_signer(accounts[0])` before
  proceeding. → "missing signer check" bug class structurally impossible.
- Verus rejects any version that doesn't `accounts.len() >= 3`. → "off-by-one
  arg count" bug class structurally impossible.
- The `apply_transfer` inside has its own verified ensures (conservation,
  signer-owner match, distinct receiver) — those properties are proven for
  the local `TokenAccount` values we read and mutate.

What we don't yet get:
- The post-state `ensures` only states `accounts.len() >= 3 && ai_signed(...)`.
  We can't state `ai_token_data(&accounts[1]).owner == ai_key(&accounts[0])`
  at the dispatch level because that requires framing — "writing to account A
  doesn't change account B's view." Verus's uninterpreted spec-function model
  treats `ai_token_data` as a pure function (same input → same output);
  there's no implicit notion of "state changed between two calls."
- We don't formally verify that the writeback goes to the *same* `AccountInfo`
  we read from. By inspection of the 6-line glue body this is correct, but
  it's not in the Verus proof.

#### Path to closing the gap

1. **Framing layer** (~1 week): introduce a "world state" parameter or
   `tracked` ghost machinery so writes to account A have an explicit
   "preserves account B" axiom. Re-state `verified_transfer_instruction`'s
   ensures with full post-state properties.
2. **Replicate to all 7 instructions** (~1 week): mechanical.
3. **Total honest estimate**: ~2–3 weeks of focused work to fully close
   Solana steps 1 + 2 as originally scoped.

Today's iteration accomplished about 30–40 % of step 1: the dispatch-level
signer/length checks (the two most common Solana exploit classes) are
covered, but the full state-tracked post-condition isn't yet.

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
