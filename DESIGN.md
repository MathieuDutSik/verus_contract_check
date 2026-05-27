# Design Decisions

This document captures the architectural choices that shaped the per-chain
verification work. Most of these emerged from concrete obstacles hit
while porting the fungible-token verification across chains; many are
not the *only* possible choice. Each section explains the decision, the
forces that drove it, and the alternative paths considered.

If you're considering changing something, this is the place to start.

---

## Project layout

```
verus_contract_check/
├── verus/                  # Initial wiring-test crate (kept; not load-bearing)
├── fungible_application_examples/
│   ├── core.rs (per chain) # Chain-agnostic State<A> + conservation lemmas
│   ├── <chain>/
│   │   ├── Cargo.toml
│   │   └── src/
│   │       ├── lib.rs      # Contract + verified helpers in verus!{}
│   │       ├── core.rs     # Copy of the chain-agnostic core
│   │       └── <chain>_axioms.rs   # Chain-specific axioms
│   └── ...
├── DESIGN.md               # This file
├── TODO.md                 # Open issues
└── README.md
```

### Why duplicate `core.rs` per chain instead of sharing it via a workspace crate?

Tried; rejected. Verus's `cargo verus verify` doesn't compose well with
Cargo workspaces (each crate is verified independently and the `vstd`
version pin is per-crate). The duplication is mechanical — when
`core.rs` changes, copy it to each chain's directory. A future
improvement would be a workspace `core` crate that all chains depend on.

---

## The verification architecture

### The three layers

Every per-chain crate has the same three-layer structure:

```
┌─────────────────────────────────────────────────────────────────────┐
│ Layer 3: chain-specific contract                                    │
│   - SDK-decorated entry points (#[near], #[entry_point], #[update]) │
│   - Plumbing: wrap chain storage in StoreRef-style wrappers,        │
│     handle the chain's Result/panic semantics.                      │
│   - The body is a 1–10-line forwarder to the verified helper.       │
├─────────────────────────────────────────────────────────────────────┤
│ Layer 2: verified helpers (inside `verus!{}` block in lib.rs)       │
│   - `verified_transfer`, `verified_mint`, etc.                      │
│   - Take a (Sized) storage reference + the runtime args.            │
│   - Body calls the verified-arithmetic core and the axiomatized     │
│     storage operations.                                             │
│   - `ensures` clause describes the effect on the abstract view.     │
├─────────────────────────────────────────────────────────────────────┤
│ Layer 1: chain-agnostic core (`core.rs`)                            │
│   - `core::transfer_balances(from, to, amt)` (executable arithmetic │
│     with conservation ensures).                                     │
│   - `core::State<A>` + `state_after_transfer` + invariant lemmas    │
│     (spec-level, generic in the account type A).                    │
└─────────────────────────────────────────────────────────────────────┘
                              │
                              │ axioms below
                              ▼
┌─────────────────────────────────────────────────────────────────────┐
│ Trust surface (`<chain>_axioms.rs`)                                 │
│   - external_type_specification: chain primitives (Addr, Principal, │
│     ActorId, AccountId, Uint128, …).                                │
│   - external_trait_specification: chain traits (BorshSerialize,     │
│     Storage, …) where applicable.                                   │
│   - Axiomatized point operations: read/write to storage maps,       │
│     caller resolution.                                              │
└─────────────────────────────────────────────────────────────────────┘
```

The architecture's value: most of layer 1 (`core.rs`) is byte-identical
across chains. Layer 2 differs in storage axioms and caller-resolution
mechanism. Layer 3 is each chain's idiomatic contract code.

### Why a generic `core::State<A>`?

Originally `pub type AccountId = int;` — concrete. Changed to `State<A>`
when porting started because each chain has its own `AccountId` type
(`near_sdk::AccountId`, `cosmwasm_std::Addr`, `candid::Principal`,
`gstd::ActorId`). Generic spec functions and lemmas reuse cleanly.

Trade-off: the type parameter needs `#[verifier::reject_recursive_types(A)]`
on the struct definition (else Verus warns about non-positive variance).
Cosmetic.

---

## Working with the Verus tool

### Verify against the wasm32 target, not the host

Discovered the hard way. Most chain SDKs (NEAR, CosmWasm, Gear, ink!, …)
explicitly refuse to compile on host targets — they emit `compile_error!`
or use `#[cfg(target_family = "wasm")]` gates. Verifying via
`cargo verus verify --target wasm32-unknown-unknown` satisfies these
gates and lets Verus parse the SDK macro expansions cleanly.

Concretely:
```
cargo verus verify --target wasm32-unknown-unknown
```

For Verus's pinned Rust toolchain to have wasm32:
```
rustup target add wasm32-unknown-unknown --toolchain 1.95.0-aarch64-apple-darwin
```

### Pin the Verus install to a tagged release

Verus's `vstd` is published to crates.io tied to a specific release tag.
If your local Verus tree drifts past that tag (e.g., `git pull` on
`main`), `cargo verus verify` fails with trait-bound mismatches inside
vstd. Fix: check the Verus checkout out at the matching release tag and
rebuild.

```
cd ~/opt/verus
git checkout release/0.2026.05.17.e479cce
cd source && source ../tools/activate && vargo build --release
```

The pin is brittle. A future improvement would be `[patch.crates-io]`
mapping `vstd` to the local source.

### Use `default-features = false, features = ["alloc"]` on `vstd` for no_std chains

Default `vstd` pulls in `std`. Chains like Gear (`no_std` with their own
`panic_impl`) get a duplicate-lang-item error. Workaround:

```toml
vstd = { version = "=0.0.0-2026-05-17-0151", default-features = false, features = ["alloc"] }
```

vstd has clean `alloc`-only support; we just need to opt into it.

### Per-Cargo.toml boilerplate every chain needs

```toml
[dependencies]
vstd = "=0.0.0-2026-05-17-0151"        # exact pin; or alloc-only as above

[package.metadata.verus]
verify = true

[lints.rust]
unexpected_cfgs = { level = "warn", check-cfg = ['cfg(verus_only)'] }
```

`cfg(verus_only)` is set by `cargo verus` during verification. Items
that exist only for the verifier (typically `use vstd::map::*;` etc.)
should be `#[cfg(verus_only)]`-gated to avoid unused-import warnings
during normal `cargo build`.

---

## Storage axiomatization patterns

The chain-specific axiomatization is the dominant per-chain cost.
Different chains forced different wrapping strategies:

| chain | underlying primitive | wrapper / approach |
|---|---|---|
| NEAR | `LookupMap<K, V, Identity>` | `AxLookupMap<K, V>` newtype |
| CosmWasm | `dyn Storage` + `Map<K, V>` const | `StoreRef<'_>` + `StoreRefRead<'_>` newtype, axiomatized point ops |
| IC | `BTreeMap<K, V>` (std) | thin `read_balance`/`save_balance` wrappers (no newtype) |
| Gear | `hashbrown::HashMap<K, V>` | `AxHashMap<K, V>` newtype |
| MultiversX | `BigUint<M>` (managed type, `M: ManagedTypeApi`) | trait-cascade pattern (see below) + specialized point ops |
| linera_alternate | `SyncMapView<C, K, V>` (3-param, `C: SyncContext`) | trait-cascade pattern + concrete-`C` specialization + point ops |

### The trait-cascade pattern (`MultiversX` / `linera_alternate`)

External traits with multiple super-traits can be axiomatized via
`external_trait_specification` by listing the **external** super-traits
directly in the proxy's super-trait header:

```rust
#[verifier::external_trait_specification]
pub trait ExManagedTypeApi: HandleTypeInfo + StaticVarApi + ErrorApi + Clone + 'static {
    type ExternalTraitSpecificationFor: ManagedTypeApi;
}
```

What did *not* work (we tried):

- `type ExternalTraitSpecificationFor: ManagedTypeApi + HandleTypeInfo + ...;` — "only one bound allowed in ExternalTraitSpecificationFor"
- `where Self::ExternalTraitSpecificationFor: HandleTypeInfo, ...` on the associated type — "bounds don't match"
- `where <Self as ExManagedTypeApi>::ExternalTraitSpecificationFor: ...` on the trait — "only one bound allowed"
- `pub trait ExManagedTypeApi: ExHandleTypeInfo + ExStaticVarApi + ExErrorApi { ... }` — Verus sees the inherited bounds but doesn't equate proxy names with their external counterparts

The working form puts the *external* trait names in the proxy's
super-trait list. Verus folds those into bounds on
`Self::ExternalTraitSpecificationFor` and matches them against the
super-trait closure of the proxied trait. The associated type still
declares exactly one bound (the trait being proxied).

This pattern generalizes — same fix unblocked both MultiversX's
`BigUint<M>` and linera_alternate's `SyncMapView<C, K, V>`.

NB: this does *not* help NEAR's `Sealed` blocker (the super-trait's
path is private and can't be referenced) or Gear's `hashbrown::HashMap`
blocker (those are unknown *type parameters*, not super-traits). The
newtype-wrapper escape hatch still applies to those.

### Why NEAR needs a wrapper (`AxLookupMap`)

`near_sdk::store::key::ToKey` has `Sealed` as a private super-trait in
`near_sdk::store::key::private`. Verus's `external_trait_specification`
requires the proxy trait's super-traits to match exactly — but we can't
reference a private path. Specializing the wrapper to the default
`Identity` hasher (which Verus *can* see) sidesteps the issue.

Cost: alternate hashers (`Sha256`, `Keccak256`) aren't supported by this
wrapper. A future Verus extension allowing private super-traits in
trait specs would let us drop the wrapper.

### Why CosmWasm needs newtype storage wrappers (`StoreRef`/`StoreRefRead`)

Verus doesn't yet support the `&mut dyn Trait → &mut dyn Trait`
reborrow. This means generic `<S: Storage>` parameters work but the
unbounded `&mut dyn Storage` (which is what `DepsMut.storage` is) doesn't
compose. Wrapping it in our own `StoreRef<'a>(pub &'a mut dyn Storage)`
gives Verus a concrete Sized type to reason about.

The unverified glue cost is ~8 lines per CosmWasm contract for the
wrapper + entry-point conversions. Manageable.

### Why IC didn't need a struct wrapper

vstd has `std_specs::btree` with `assume_specification` for
`BTreeMap`'s methods. *In principle* this works directly. *In practice*
vstd's specs use `Borrow<Q>`-based helper predicates
(`maps_borrowed_key_to_value`, `contains_borrowed_key`) that add a
layer of indirection in proofs. We chose tiny per-operation wrappers
(`read_balance`, `save_balance`) with simpler specs over wrestling
with vstd's BTreeMap surface.

The wrappers are 4 lines each. The cost is that we lose the ability
to call other BTreeMap operations directly with the simple shape.
Acceptable for fungible-token; might revisit if we need more.

### Why Gear needs a newtype wrapper (`AxHashMap`)

`hashbrown::HashMap` has many transitive type parameters
(`BuildHasherDefault`, `AHasher`, `allocator_api2::Global`) that Verus
flags as unknown unless each has an `external_type_specification`.
Wrapping `HashMap` in `AxHashMap` (`external_body` opaque struct)
hides all of them at once.

---

## Caller / sender resolution

Every chain has a notion of "who's calling this method." We axiomatize
this uniformly via an uninterpreted ghost spec function plus a
Verus-aware wrapper around the runtime call.

| chain | runtime call | ghost spec |
|---|---|---|
| NEAR | `env::predecessor_account_id()` | `the_caller() -> AccountId` |
| CosmWasm | `MessageInfo.sender` (direct param) | not needed — sender is a normal function arg |
| IC | `ic_cdk::api::caller()` | `the_caller() -> Principal` |
| Gear | `gstd::msg::source()` | `the_sender() -> ActorId` |

Each uninterpreted spec function is *constant within a verification
session*. Calling the wrapped function twice in one verified method
yields the same Verus value — exactly what the runtime guarantees.

CosmWasm is the outlier: `info.sender` is passed as a parameter to
`execute`, so no env-side axiomatization is needed.

### Why not just an opaque function with no spec?

Considered. The issue is that callers want to reason about *what* the
returned value is. With an uninterpreted spec function `the_caller()`,
the ensures of `verified_transfer` can say:

```rust
ensures the_caller() != receiver,
        balances@_after == ...the_caller()...
```

Without it, we'd have no way to express "the caller wasn't the
receiver" or "the right account was debited."

---

## Conservation: `u128` vs `nat`

### Why two number types?

- **Exec code uses `u128`** because that's what the SDKs use.
- **Spec code (`core::State<A>`, `sum_balances`) uses `nat`** (Verus's
  unbounded non-negative integer).

`nat` lets us reason mathematically without overflow constraints.
`u128` is what's actually in the contract storage. The refinement
lemmas bridge them.

### The `nat_balances` lift function

```rust
spec fn nat_balances(m: SpecMap<Addr, u128>) -> SpecMap<Addr, nat> {
    SpecMap::new(
        |a| m.dom().contains(a),
        |a| m[a] as nat,
    )
}
```

Point-wise cast at the spec level. The exec storage holds `u128`
values; `core::State`'s balances field holds `nat` values; `nat_balances`
takes one to the other.

### The conditional refinement ensures

`verified_transfer`'s ensures includes a *conditional* state-level
clause:

```rust
ensures (balances_view_pre.dom().contains(sender)
         && balances_view_pre.dom().contains(receiver)
         && balances_view_pre[receiver] + amount <= u128::MAX
         ==> nat_balances(balances_view_post)
              == core::state_after_transfer(...).balances)
```

The conditional is necessary because:
- `core::state_after_transfer`'s `recommends` requires both accounts
  to be in the map's domain.
- The runtime `verified_transfer` handles absent entries (treats as 0).
- For the absent-entry case, the state-level connection is meaningless.

Trade-off: the ensures is longer. Callers who want the conservation
theorem must establish the dom-contains preconditions before chaining.

---

## Error handling: panic vs Result

Two patterns coexist in the codebase:

- **NEAR, Gear**: contract methods panic on failure (`env::panic_str`,
  `panic!`). We model this with a Verus-aware `panic_str(msg)` that has
  `ensures false`, modeling divergence.
- **CosmWasm, IC**: contract methods return `Result<_, _>`. We define
  a local `TransferError` enum *inside* the `verus!{}` block (so Verus
  can reason about it) and convert to the chain's `ContractError` /
  `String` at the entry point.

Both are honest reflections of the chains' idioms. Result-returning
is slightly easier for Verus (no divergence reasoning needed), but the
contract source ends up with a `match e` ladder at every call site.

### The `TransferError` enum

Defined per-chain inside the `verus!{}` block. Always includes:
- `SelfTransfer` — caller and recipient are the same.
- `Insufficient` — balance underflow.
- `Overflow` — recipient balance overflow.

For chains with cw20-style allowances:
- `InsufficientAllowance`
- `Unauthorized` (for mint, update_minter)

---

## Generic vs `?Sized` storage parameters

CosmWasm's `dyn Storage` forced us to choose between:

- `<S: Storage>` (Sized only) — works inside Verus; but `dyn Storage`
  can't be passed because it's unsized. Required adding a `StoreRef`
  wrapper at the entry point.
- `<S: Storage + ?Sized>` — would accept `dyn Storage` but the body
  fails to compile (coercing `&mut S` to `&mut dyn Storage` to call
  SDK methods needs `S: Sized`).

We chose Sized + StoreRef. The wrapper boilerplate is ~10 lines per
contract. The alternative is to file a Verus issue and wait for upstream
dyn-reborrow support.

---

## Macro-decorated entry points

Each chain's SDK uses macros to register entry points:

| chain | macros |
|---|---|
| NEAR | `#[near(contract_state)]`, `#[near]` |
| CosmWasm | `#[entry_point]` |
| IC | `#[init]`, `#[query]`, `#[update]` |
| Gear | bare `extern "C" fn handle()` |
| ink! | `#[ink::contract]` (wraps a whole module) |
| MultiversX | `#[multiversx_sc::contract]` (wraps a whole trait) |

**These methods cannot easily be put inside `verus!{}` blocks**: the
macros expand into wasm bindings, panic handlers, and ABI marshalling
that Verus can't parse.

Resolution: each `#[macro]`-decorated entry point is a thin forwarder
(usually 1–10 lines) to a `verified_*` helper that lives inside
`verus!{}`. The forwarder is unverified glue; the verified helper has
all the substantive logic and ensures clauses.

For NEAR's `Fungible::transfer` we got the forwarder down to **one
line**:

```rust
pub fn transfer(&mut self, receiver: AccountId, amount: u128) {
    verified_transfer(&mut self.balances, receiver, amount);
}
```

For CosmWasm's `execute` Transfer branch the forwarder is ~5 lines
(StoreRef wrap + error mapping).

---

## What's deliberately *not* verified

For honesty, here's what each verified contract leaves unverified:

1. **The macro expansion itself** (#[near], #[ink::contract], etc.).
   Trusting the SDK to expand to functionally-correct code.

2. **The wasm bindings** (extern "C" fn dispatch). Trusting the chain's
   wasm runtime to call the right entry point with the right arguments.

3. **The `static mut STATE` access in Gear** and the `thread_local!
   RefCell<State>` access in IC. Trusting that the state is properly
   initialized and accessed atomically.

4. **The Borsh/Serde derive macros** on the contract's message types.
   Trusting that serialization round-trips correctly.

5. **Sub-message / callback dispatch** (CosmWasm `SubMsg`, NEAR
   `Promise`, IC inter-canister calls). Documented in TODO.md.

6. **The chain runtime itself** — e.g., that `env::predecessor_account_id()`
   actually returns the caller, that `Storage::set` actually persists.
   These are the axiomatized chain semantics; we trust the chain to
   implement them.

The unverified surface per contract is typically:
- 1–10 lines of glue per entry point,
- ~5–25 lines of chain axioms,
- the trusted-but-axiomatized chain-runtime behavior.

In return: the entire substantive logic — arithmetic, conservation,
storage refinement, authorization — is formally verified.

---

## Patterns that worked across chains

1. **Verus block in `lib.rs`, not a separate crate.** Tried separate
   crate first (`verus_contract_check/verus/`); abandoned because each
   chain needs its own helpers tied to its types. The separate-crate
   experiment is left in the tree as documentation.

2. **`(r: TYPE)` named return values** for ensures clauses. Verus syntax:
   `pub fn foo(...) -> (r: u128) ensures r == ...`.

3. **`#[verifier::external_body]` for trusted wrappers.** Function body
   is hidden from Verus; only the `ensures` is the contract.

4. **`assert(... =~= ...)` for extensional map equality.** The `=~=`
   operator triggers Verus's extensionality reasoning; bare `==` often
   doesn't see two maps as equal even when they semantically are.

5. **`assert forall|k| ... by { ... }` for goal-directed quantifier
   proofs.** Combines `forall` with a per-bound-variable proof body,
   often case-split on `k`.

6. **`#[allow(dead_code)] field` inside external_type_specification proxy
   structs.** The field is needed for Rust type inference but never read.

7. **`#![cfg_attr(not(test), no_std)]` for no_std chains.** Lets `cargo
   test` use std; deploys remain no_std.

---

## Choices we might revisit

These are decisions that worked but might not be the best long-term:

1. **Per-chain `core.rs` duplication.** A workspace `core` crate would
   be cleaner. Blocked on figuring out `cargo verus verify`'s workspace
   handling.

2. **`u128` everywhere instead of using NEAR's `U128` JSON wrapper.**
   We use raw `u128` and convert at the boundary in tests. Real NEP-141
   uses `U128` for JSON compatibility. Add a JSON-wrapper conversion
   if/when we generate Candid/JSON schemas.

3. **`TransferError` as a per-chain enum.** Could be shared in `core.rs`
   if we wanted, but each chain maps it to a chain-specific error type
   (`ContractError`, `String`, `&'static str`). The duplication is small.

4. **No `view_fungible(&Fungible) -> State` lift.** The state-level
   refinement happens at the map level, not the struct level. Lifting
   the macro-wrapped `Fungible` struct to a `core::State` would require
   `external_type_specification` for `Fungible` + field-access axioms.
   Currently unverified gap.

5. **No verification of mint/burn auth in NEAR/Gear.** Only CosmWasm
   and IC have it. Easy to add.

6. **No state-level connection lemma applied in IC/Gear's
   `verified_transfer`.** Easy to port from CosmWasm; not done yet
   because the existing tests / verification surface are sufficient.

---

## Glossary

- **Chain-agnostic** — code that doesn't reference any specific
  blockchain SDK (`core.rs`).
- **Verified helper** — a function inside `verus!{}` with `ensures`
  clauses that Verus proves.
- **Axiom** — a function or trait marked `#[verifier::external_body]`
  or `assume_specification` whose ensures Verus trusts without
  checking.
- **Conservation invariant** — `sum_balances(state.balances) ==
  state.total_supply`. The fundamental property of a fungible token.
- **Refinement lemma** — proves that a runtime (`u128`) operation
  corresponds to a spec-level (`nat`) operation. Bridges layers 1 and 2.
- **State-level ensures** — the conditional clause in `verified_*`
  helpers' ensures that connects to `core::state_after_*`.
- **TCB (Trusted Computing Base)** — the axioms + glue we accept
  without verification. Per-chain typically ~30 lines.
