# application_examples

Parallel implementations of the same minimal fungible-token contract across the
eight smart-contract platforms we are considering for Verus-based
axiomatization and verification.

Each contract exposes the same three operations, with platform-idiomatic types:

- `init` / `instantiate` / `constructor`: set initial total supply, credit it to the deployer (or to an explicit `owner` argument where the platform's call model makes that more natural).
- `transfer(to, amount)`: signed by the source; subtracts from the caller's balance and adds to `to`'s balance. Checks for underflow and overflow; rejects self-transfer.
- `balance_of(account)` / query: read-only view of one account's balance.
- `total_supply()`: read-only view of the supply (invariant: equals the sum of all balances after every operation).

The contracts are deliberately minimal — no allowances, no metadata, no decimals, no events beyond what each platform requires. The goal is to give a single artifact we can axiomatize against eight different runtime semantics.

## Layout

```
application_examples/
  linera/        linera-sdk Contract/Service split, View-based state
  near/          near-sdk #[near_bindgen] with LookupMap balances
  solana/        native solana-program with Borsh-serialised account data
  gear/          gstd actor with init/handle message handlers
  multiversx/    multiversx-sc trait-based contract
  ic/            ic-cdk canister with #[init]/#[update]/#[query]
  ink/           ink! v5 contract with Mapping storage
  cosmwasm/      cosmwasm-std entry points with cw-storage-plus
```

Each subdirectory is a standalone Cargo crate with its own `Cargo.toml`.
SDK versions are pinned to recent releases as of the time of writing; expect to bump them as upstream evolves.

## Cross-chain shape of the same logic

| Platform | Caller identity | Storage primitive | Money type | Entry-point style |
|---|---|---|---|---|
| Linera | `AccountOwner` from `authenticated_signer` | `MapView<K,V>` + `RegisterView<T>` | `u128` | async `Contract::execute_operation` |
| NEAR | `env::predecessor_account_id()` | `LookupMap<AccountId, u128>` | `u128` | `#[near_bindgen]` methods |
| Solana | `AccountInfo.is_signer` | account-data buffers (Borsh) | `u128` | `entrypoint!(process_instruction)` |
| Gear | `msg::source()` | global `static mut` + `HashMap` | `u128` | `extern "C" fn init/handle` |
| MultiversX | `self.blockchain().get_caller()` | `SingleValueMapper` | `BigUint` | `#[multiversx_sc::contract]` trait |
| IC | `ic_cdk::api::caller()` | `thread_local!` `BTreeMap` | `u128` | `#[init]`/`#[update]`/`#[query]` |
| ink! | `self.env().caller()` | `ink::storage::Mapping` | `Balance` | `#[ink(message)]` methods |
| CosmWasm | `MessageInfo.sender` | `Item`/`Map` via `cw-storage-plus` | `Uint128` | `instantiate`/`execute`/`query` entry points |

The common-denominator shape is always the same: a `(caller, recipient, amount)` triple, two balance reads, two checked-arithmetic updates, two balance writes.

## Roadmap toward verification

These crates are presently **unverified**: standard Rust + each platform's SDK, with `checked_sub` / `checked_add` to fail closed rather than silently wrap.

The intended next steps:

1. Extract a chain-agnostic core (`spec fn balance(s, a) -> nat`, `spec fn transfer_post(s, from, to, amt) -> State`) and prove transfer respects the invariant `sum(balances) == total_supply` in pure Verus.
2. For each chain, write a `chain_axioms.rs` module containing `#[verifier::external_body]` lemmas that model the runtime's host calls (caller authentication, storage read/write semantics, message dispatch).
3. Replace the SDK calls in each contract with shims whose `requires/ensures` match the axioms, so the same verified core can be re-targeted at each chain.

Step 1 is what's worth doing first — it surfaces what is genuinely common across the eight runtimes and what is not (signed messages vs. account-list authority on Solana, sync vs. async cross-contract calls on NEAR/Linera, etc.).
