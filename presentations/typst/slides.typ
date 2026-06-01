// 25-minute talk: cross-chain smart-contract verification with Verus.
// Audience: Ethereum-background engineers (interview context).
//
// Build:   typst compile slides.typ
// Watch:   typst watch slides.typ
//
// One #pagebreak() per slide. Headings act as slide titles.

#set page(
  paper: "presentation-16-9",
  margin: (x: 1.6cm, y: 1.2cm),
)
#set text(size: 22pt, font: "Helvetica")
#set par(leading: 0.7em)

#show heading.where(level: 1): it => {
  block(below: 0.6em)[
    #set text(size: 32pt, weight: "bold")
    #it.body
  ]
  line(length: 100%, stroke: 1pt + rgb("#777"))
  v(0.4em)
}
#show heading.where(level: 2): set text(size: 24pt, weight: "bold")

#let small = body => text(size: 18pt, body)
#let code = body => raw(body, lang: "rust")

// ===================================================================
// Slide 1 — Title
// ===================================================================
#align(center + horizon)[
  #text(size: 38pt, weight: "bold")[
    Cross-Chain Smart-Contract Verification
  ]
  #v(0.3em)
  #text(size: 26pt)[
    Eight Platforms, One Proof Kernel
  ]
  #v(2em)
  #text(size: 22pt)[
    Mathieu Dutour Sikirić
  ]
  #v(0.3em)
  #text(size: 18pt, fill: rgb("#555"))[
    Using Verus to verify fungible-token logic across\
    CosmWasm · NEAR · IC · Gear · ink! · MultiversX · Solana · Linera
  ]
]

#pagebreak()

// ===================================================================
// Slide 1b — Project principle
// ===================================================================
= The principle of the project

#v(0.3em)

- *Target Rust-based smart-contract platforms.*\
  #small[Verus annotates Rust directly, so any chain whose contracts are Rust (or compile via Rust) is in scope. That covers eight major non-EVM platforms.]

#v(0.4em)

- *Verification code lives next to the Rust it verifies.*\
  #small[`requires` / `ensures` / `proof` blocks sit in the same crate as the code that compiles to wasm. No separate spec artifact to drift.]

#v(0.4em)

- *Axiomatize each blockchain's host semantics.*\
  #small[SDK types (storage maps, big integers, caller APIs) are declared external; ~30 lines of trusted axioms per chain capture what the runtime guarantees.]

#v(0.4em)

- *Discharge to Z3.*\
  #small[Classic SMT back-end. Quantifier-free arithmetic and map theories handle the bulk; the proof obligations come from the annotations.]

#v(0.4em)

- *Decompose the hard parts into lemmas.*\
  #small[Conservation, refinement from `nat` to `u128`, state-level invariants — each proved once as a reusable lemma, then applied at every call site.]

#pagebreak()

// ===================================================================
// Slide 2 — Hook
// ===================================================================
= The bug we want to make impossible

A fungible-token contract holds a balance map and a `total_supply` field.

#v(0.5em)

The invariant every honest implementation should satisfy:

#align(center)[
  #box(stroke: 1pt + rgb("#444"), inset: 0.7em, radius: 4pt)[
    $sum_(a in "accounts") "balance"(a) = "total_supply"$
  ]
]

#v(0.5em)

The bug class:
- *Compound* (Sep 2021): MASTER inflation, \$80M.
- *USDC* (theoretical via faulty `_mint`): unbounded creation.
- *TheDAO* (Jun 2016): not conservation per se, but a different invariant violated.

#v(0.5em)

#small[A single overflow on `to_balance + amount` and the sum no longer matches the supply. Tests with concrete inputs cannot prove the invariant holds for *all* inputs.]

#pagebreak()

// ===================================================================
// Slide 3 — Tests vs. proofs
// ===================================================================
= Tests check examples. Proofs check classes.

#grid(
  columns: (1fr, 1fr),
  gutter: 1em,
  [
    *Testing*
    - Pick inputs `(from, to, amount)`.
    - Run the contract.
    - Assert post-state.
    - Catches the bugs you thought of.
  ],
  [
    *Verification*
    - Assert a property for *all* inputs.
    - Verifier searches for a counter-model.
    - Either a proof, or a witness.
    - Catches the bugs you didn't.
  ],
)

#v(1em)

We want this to be a *theorem*:

#align(center)[
  #box(stroke: 1pt + rgb("#444"), inset: 0.7em, radius: 4pt)[
    #set text(size: 20pt)
    For any pre-state $s$, any `(from, to, amount)`, if `transfer` returns Ok\
    then $"sum"("balances")$ in the post-state equals $"sum"("balances")$ in $s$.
  ]
]

#pagebreak()

// ===================================================================
// Slide 4 — Verus in one slide
// ===================================================================
= Verus in one slide

#small[
*Refinement-typed Rust*. You annotate the same Rust that compiles to wasm; the verifier checks the annotations match the body. No separate spec language.
]

#v(0.3em)

```rust
pub fn transfer_balances(
    from_balance: u128, to_balance: u128, amount: u128,
) -> (r: Result<(u128, u128), &'static str>)
    ensures match r {
        Ok((from_next, to_next)) =>
            from_next + to_next == from_balance + to_balance     // conservation
            && from_next == from_balance - amount
            && to_next == to_balance + amount,
        Err(_) =>
            from_balance < amount || to_balance + amount > u128::MAX,
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
```

#small[Verus discharges this to Z3. ~1 second on a laptop. The function *cannot* be implemented incorrectly and still typecheck.]

#pagebreak()

// ===================================================================
// Slide 5 — Cross-chain framing
// ===================================================================
= The question this work answers

#v(0.5em)

Most verification work targets one platform.
EVM/Solidity is the obvious one (K-framework, Certora, Slither).

#v(1em)

But there are *eight major non-EVM smart-contract platforms*:

#align(center)[
  #box(inset: 0.5em)[
    *CosmWasm · NEAR · Internet Computer · Gear · ink! ·*\
    *MultiversX · Solana · Linera*
  ]
]

#v(1em)

Each has its own SDK, storage primitive, caller-resolution mechanism, error idiom. *Naïve verification = one project per chain.*

#v(1em)

#align(center)[
  #text(weight: "bold", size: 26pt)[
    What is the right *shape* of a verification project so that the proof is portable?
  ]
]

#pagebreak()

// ===================================================================
// Slide 6 — Eight chains compared
// ===================================================================
= Eight chains, eight runtime shapes

#set text(size: 16pt)

#table(
  columns: (auto, auto, auto, auto),
  inset: 7pt,
  align: left,
  table.header(
    [*Chain*], [*Caller*], [*Storage primitive*], [*Money type*],
  ),
  [CosmWasm],   [`MessageInfo.sender`],         [`Map<K,V>` via cw-storage-plus],     [`Uint128`],
  [NEAR],       [`env::predecessor_account_id()`], [`LookupMap<K, V, Identity>`],     [`u128`],
  [IC],         [`ic_cdk::api::caller()`],      [`thread_local!` `BTreeMap`],          [`u128`],
  [Gear],       [`msg::source()`],              [`static mut` + `HashMap`],            [`u128`],
  [ink!],       [`Self::env().caller()`],       [`ink::storage::Mapping`],             [`Balance` (u128)],
  [MultiversX], [`self.blockchain().get_caller()`], [`SingleValueMapper`],            [`BigUint` (unbounded)],
  [Solana],     [`AccountInfo.is_signer`],      [account-data buffers (Borsh)],        [`u128`],
  [Linera],     [`runtime.authenticated_signer`], [`SyncMapView<K,V>`],                [`Amount` (newtype u128)],
)

#v(0.6em)
#small[
The common shape is always the same: *(caller, recipient, amount) → two balance reads → two checked-arithmetic updates → two writes.* The question is how much of that can be one proof.
]

#pagebreak()

// ===================================================================
// Slide 7 — Three-layer architecture
// ===================================================================
= The three-layer architecture

#align(center)[
  #set text(size: 18pt)
  #box(stroke: 1pt + rgb("#444"), inset: 1em, radius: 4pt, width: 90%)[
    *Layer 3 — chain-specific entry points*\
    `#[entry_point]` / `#[update]` / `#[ink(message)]` / `extern "C" fn handle()`...\
    1–10 lines of *unverified* glue per entry. Forwards to:
  ]
  #v(0.4em)
  $arrow.b$
  #v(0.4em)
  #box(stroke: 1pt + rgb("#0a7"), inset: 1em, radius: 4pt, width: 90%, fill: rgb("#e0f5e0"))[
    *Layer 2 — verified helpers* (inside `verus!{}`)\
    `verified_transfer(storage, sender, receiver, amount) -> Result<...>`\
    Reads, runs arithmetic, writes. `ensures` describes the abstract storage delta.
  ]
  #v(0.4em)
  $arrow.b$ #h(2em) calls $arrow.b$
  #v(0.4em)
  #box(stroke: 1pt + rgb("#07a"), inset: 1em, radius: 4pt, width: 90%, fill: rgb("#e0e8f5"))[
    *Layer 1 — chain-agnostic core* (`verus_fungible_core` crate)\
    `transfer_balances : u128, u128, u128 → Result<...>` + conservation lemmas on `State<A>`.\
    *Byte-identical across all eight chains.*
  ]
  #v(0.4em)
  #box(stroke: (paint: rgb("#a00"), thickness: 1pt, dash: "dashed"), inset: 0.5em, radius: 4pt, width: 90%)[
    *Trust surface — `<chain>_axioms.rs`*: external_type_specification for SDK types, point-op storage axioms, caller ghost.
  ]
]

#pagebreak()

// ===================================================================
// Slide 8 — The conservation theorem at the spec level
// ===================================================================
= Conservation, stated once for all chains

#small[Inside the shared core crate, generic over the chain's account-id type `A`:]

```rust
pub struct State<A> {
    pub total_supply: nat,
    pub balances: Map<A, nat>,         // unbounded-precision in the spec
}

impl<A> State<A> {
    pub open spec fn invariant(self) -> bool {
        self.balances.dom().finite()
        && sum_balances(self.balances) == self.total_supply
    }
}

pub proof fn lemma_transfer_preserves_invariant<A>(
    s: State<A>, from: A, to: A, amount: nat,
)
    requires s.invariant(), from != to,
             s.balances.dom().contains(from), s.balances.dom().contains(to),
             s.balances[from] >= amount,
    ensures state_after_transfer(s, from, to, amount).invariant(),
{ /* 15-line proof by induction on the map's domain */ }
```

#v(0.4em)

#small[*Proven once, reused eight times.* Bridge to `u128` is a separate refinement lemma, also in the shared crate.]

#pagebreak()

// ===================================================================
// Slide 9 — Case 1: CosmWasm (the clean case)
// ===================================================================
= Case 1: CosmWasm — what "done" looks like

#small[
The whole cw20 surface — `transfer`, `approve`, `transfer_from`, `mint`, `burn`, `increase_allowance`, `decrease_allowance`, `update_minter` — is routed through verified helpers.
]

#v(0.3em)

```rust
#[entry_point]
pub fn execute(deps: DepsMut, _env: Env, info: MessageInfo, msg: ExecuteMsg)
    -> Result<Response, ContractError>
{
    let mut store_ref = StoreRef(deps.storage);
    match msg {
        ExecuteMsg::Transfer { recipient, amount } => {
            let to = deps.api.addr_validate(&recipient)?;
            verified_transfer(&mut store_ref, &info.sender, &to, amount.u128())
                .map_err(map_transfer_error)?;
            Ok(Response::new().add_attribute("action", "transfer"))
        }
        // ... 7 more branches, each a forwarder ...
    }
}
```

#v(0.3em)

#small[
*11 verified obligations* in CosmWasm + *12 in the shared core* = the substantive arithmetic, storage refinement, authorization, and state-level connection. *24 unit tests* still pass. Unverified glue: the `entry_point` macro expansion and the `addr_validate` SDK call (~5 lines per branch).
]

#pagebreak()

// ===================================================================
// Slide 11 — The trait-cascade obstacle
// ===================================================================
= The obstacle, and the discovery

`BigUint<M: ManagedTypeApi>` requires Verus to know `ManagedTypeApi`, which has *five super-traits*:

#align(center)[
  `ManagedTypeApi: HandleTypeInfo + StaticVarApi + ErrorApi + Clone + 'static`
]

#v(0.5em)

Three forms I tried failed:

#small[
1. `type ExternalTraitSpecificationFor: ManagedTypeApi + HandleTypeInfo + ...;`\
  → *only one bound allowed*.
2. `where Self::ExternalTraitSpecificationFor: HandleTypeInfo, ...` on the associated type → *bounds don't match exactly*.
3. Proxy-trait inheritance `pub trait ExManagedTypeApi: ExHandleTypeInfo + ...` → Verus sees the inherited bounds but *doesn't equate proxy names with external trait names*.
]

#v(0.5em)

The form that *does* work — put the external traits in the proxy's super-trait list directly:

```rust
#[verifier::external_trait_specification]
pub trait ExManagedTypeApi:
    HandleTypeInfo + StaticVarApi + ErrorApi + Clone + 'static
{
    type ExternalTraitSpecificationFor: ManagedTypeApi;
}
```

#small[*Same fix unblocked Linera's `SyncMapView<C, K, V>`*. Pattern is now in the project's DESIGN.md.]

#pagebreak()

// ===================================================================
// Slide 14 — Comparison
// ===================================================================
= Where this sits in the verification landscape

#set text(size: 18pt)

#table(
  columns: (auto, auto, auto),
  inset: 8pt,
  align: left,
  table.header([*Tool*], [*Target*], [*Style*]),
  [K framework],  [EVM bytecode],          [operational semantics, symbolic execution],
  [Certora],      [Solidity / Yul],        [CVL spec language, SMT],
  [Slither / Mythril], [Solidity],         [static analysis, bug-finding],
  [Halmos / Foundry-invariant], [Solidity], [bounded symbolic / property testing],
  [*Verus (this work)*], [*Rust → wasm*], [*refinement on production code*],
)

#v(0.6em)

#small[
*The differentiator*: Verus annotations live on the same Rust code that compiles to the deployed wasm. No separate spec artifact to drift. Any chain whose contract language is Rust (or compiles via Rust) is in scope — including most non-EVM chains.
]

#v(0.6em)

#small[
*The tradeoff*: each chain's host semantics is an axiom you write by hand. ~30 lines per chain, trusted, kept small.
]

#pagebreak()

// ===================================================================
// Slide 15 — Open problems
// ===================================================================
= Open problems

*1. Cross-contract dispatch (reentrancy).*\
#small[
Every chain has it: CosmWasm `SubMsg`, NEAR `Promise`, Solana CPI, IC inter-canister, Linera cross-microchain messages. Today's verification stops at one contract's boundary. Cleanly modelling "between our return and the reply, an attacker can re-enter" requires an uninterpreted-relation framing. ~2–4 weeks per chain. *This is where production-cw20 bugs concentrate.*
]

#v(0.6em)

*2. State-level connection on intermediate chains.*\
#small[
IC, Linera have verified kernels but no `nat_balances`-bridged conservation theorem at the entry point. Mechanical port from CosmWasm.
]

#v(0.6em)

*3. The Solana framing layer.*\
#small[
Write A doesn't change Account B's view, but our pure-function ghost model doesn't say that. Needs explicit `tracked` ghost state. ~1 week.
]

#v(0.6em)

*4. MultiversX `SingleValueMapper`* and *Linera `verified_approve`*: pieces left when `OwnerSpender::new` panics on `owner == spender`. Both 2-4 days of focused work each.

#pagebreak()

// ===================================================================
// Slide 17 — Closing
// ===================================================================
#align(center + horizon)[
  #text(size: 36pt, weight: "bold")[
    Eight chains. One conservation theorem.\
    Zero verification errors.
  ]

  #v(2em)

  #text(size: 24pt)[
    The bug class that lives in fungible-token contracts since 2016\
    is now structurally impossible across this proof surface.
  ]

  #v(2em)

  #text(size: 22pt, fill: rgb("#555"))[
    Questions?
  ]
]
