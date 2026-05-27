// Re-export the chain-agnostic verified core so existing call sites
// (`crate::core::transfer_balances`, `crate::core::State`, etc.) keep working.
// The actual definitions live in the `verus_fungible_core` crate.
pub use verus_fungible_core::*;
