// Re-export the chain-agnostic verified vesting core. Actual
// definitions live in the `verus_vesting_core` crate. Kept as a
// thin re-export so the per-chain lib.rs can write
// `use crate::core::...` in the same idiom the fungible example uses.
pub use verus_vesting_core::*;
