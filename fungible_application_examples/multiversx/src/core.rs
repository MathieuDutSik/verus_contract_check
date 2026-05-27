// Re-export the chain-agnostic verified core. Actual definitions are in
// the `verus_fungible_core` crate. The module is named `fungible_core`
// (not `core`) at the use site because `::core` is referenced by the
// multiversx-sc macro expansion.
pub use verus_fungible_core::*;
