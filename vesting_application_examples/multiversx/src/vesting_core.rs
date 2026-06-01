// Re-export the chain-agnostic verified vesting core. Renamed from
// `core.rs` because the `#[multiversx_sc::contract]` macro expansion
// references `::core::mem`, and a top-level `pub mod core;` would
// shadow that path. Same workaround the fungible MultiversX contract
// applies (it uses `fungible_core`).
pub use verus_vesting_core::*;
