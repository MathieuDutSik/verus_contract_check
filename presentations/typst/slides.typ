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
    Rust Smart-Contract Verification
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

#v(0.2em)

#small[
*Scope:* implement and verify the ERC-20 surface — `balance_of`, `transfer`, and the `approve` / `allowance` / `transfer_from` allowance machinery — across each chain.
]

#v(0.3em)

- *Target Rust-based smart-contract platforms.*\
  #small[Verus annotates Rust directly, so any chain whose contracts are Rust (or compile via Rust) is in scope. That covers eight major non-EVM platforms.]

#v(0.4em)

- *Verification code lives next to the Rust it verifies.*\
  #small[`requires` / `ensures` / `proof` blocks sit in the same crate as the code that compiles to Wasm/eBPF. No separate spec artifact to drift.]

#v(0.4em)

- *Axiomatize each blockchain's host semantics.*\
  #small[SDK types (storage maps, big integers, caller APIs) are declared external; ~30 lines of trusted axioms per chain capture what the runtime guarantees.]

#v(0.4em)

- *Discharge to Z3.*\
  #small[Classic SMT back-end. Quantifier-free arithmetic and map theories handle the bulk; the proof obligations come from the annotations.]

#v(0.4em)

- *Decompose the hard parts into lemmas.*\
  #small[Conservation, refinement from `nat` to `u128`, state-level invariants — each proved once as a reusable lemma, then applied at every call site.]

#v(0.6em)

#small[
Source: #link("https://github.com/MathieuDutSik/verus_contract_check")[`github.com/MathieuDutSik/verus_contract_check`]
]

#pagebreak()

// ===================================================================
// Slide 2 — Hook
// ===================================================================
= The bug we want to make impossible

A fungible-token contract holds a balance map and a `total_supply` field.

#v(0.3em)

The invariant every honest implementation should satisfy:

#align(center)[
  #box(stroke: 1pt + rgb("#444"), inset: 0.5em, radius: 4pt)[
    $sum_(a in "accounts") "balance"(a) = "total_supply"$
  ]
]

#v(0.3em)

The bug class:
- *Compound* (Sep 2021): MASTER inflation, \$80M.
- *USDC* (theoretical via faulty `_mint`): unbounded creation.

#small[A single overflow on `to_balance + amount` and the sum no longer matches the supply. Tests with concrete inputs cannot prove the invariant holds for *all* inputs.]

#pagebreak()

// ===================================================================
// Slide 3 — Tests vs. proofs
// ===================================================================
= Tests check examples. Proofs check classes.

#set text(size: 20pt)

#grid(
  columns: (1fr, 1fr),
  gutter: 0.8em,
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

#v(0.3em)

We want this to be a *theorem*:

#align(center)[
  #box(stroke: 1pt + rgb("#444"), inset: 0.4em, radius: 4pt)[
    #set text(size: 17pt)
    For any pre-state $s$, any `(from, to, amount)`, if `transfer` returns Ok\
    then $"sum"("balances")$ in the post-state equals $"sum"("balances")$ in $s$.
  ]
]

#pagebreak()

// ===================================================================
// Slide 4 — Verus in one slide
// ===================================================================
= Verus as it looks like

#small[
*Refinement-typed Rust*. You annotate the same Rust that compiles to Wasm/eBPF; the verifier checks the annotations match the body. No separate spec language.
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

#v(0.3em)
#small[
*Linera note:* the upstream SDK is async; we work against a *modified, synchronous SDK* so the verified core can call storage directly without an `async` boundary.
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
  [*Verus (this work)*], [*Rust → Wasm/eBPF*], [*refinement on production code*],
)

#v(0.6em)

#small[
*The differentiator*: Verus annotations live on the same Rust code that compiles to the deployed Wasm/eBPF. No separate spec artifact to drift. Any chain whose contract language is Rust (or compiles via Rust) is in scope — including most non-EVM chains.
]

#v(0.6em)

#small[
*Missing pieces vs. the Solidity ecosystem:*
- *Mutation testing.* Certora ships `gambit` / `certora.mutate` to inject mutants and score the spec's catch-rate. Verus has *no equivalent* — spec quality is currently judged by inspection.
- *Coverage-guided fuzzing.* The role of Echidna / Medusa on Solidity is filled on the Rust side by `cargo-fuzz` (libFuzzer): same property-based loop, same shrinking, complements but does not replace the proofs.
]

#pagebreak()

// ===================================================================
// Slide 15 — Open problems
// ===================================================================
= Open problems

*1. Cross-contract dispatch (reentrancy).*\
#small[
Every chain has it: CosmWasm `SubMsg`, NEAR `Promise`, Solana CPI, IC inter-canister, Linera cross-microchain messages. Today's verification stops at one contract's boundary. Cleanly modelling "between our return and the reply, an attacker can re-enter" requires an uninterpreted-relation framing. *This is where production-cw20 bugs concentrate.*
]

#v(0.6em)

*2. State-level connection on intermediate chains.*\
#small[
IC, Linera have verified kernels but no `nat_balances`-bridged conservation theorem at the entry point. Mechanical port from CosmWasm.
]

#v(0.6em)

*3. Per-chain structural challenge.*\
#small[
Each platform has one feature that resists a uniform verification story:
- *CosmWasm* — `SubMsg` / reply dispatch.
- *NEAR* — SDK encapsulation (sealed traits) and the `Promise` async model.
- *Internet Computer* — inter-canister calls and orthogonal persistence.
- *Gear* — actor-style message passing over `static mut` global state.
- *ink!* — opaque `Mapping` storage, hard to axiomatize cleanly.
- *MultiversX* — managed-type trait machinery (`BigUint`, `ManagedTypeApi`).
- *Solana* — account-data model: many mutable account views, no native map.
- *Linera* — the *microchain* architecture and cross-microchain messaging.
]
