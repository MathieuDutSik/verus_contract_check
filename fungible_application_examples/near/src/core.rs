// Re-export the chain-agnostic verified core. Actual definitions are in
// the `verus_fungible_core` crate. NEAR's prior local copy had diverged
// (missing mint/burn lemmas); the re-export restores the full surface.
pub use verus_fungible_core::*;
