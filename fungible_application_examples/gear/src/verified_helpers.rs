// Verified kernels that Gear's `handle()` entry point forwards to.
//
// `apply_transfer` is the test-injectable kernel; `verified_transfer`
// is the runtime-facing wrapper that reads `msg::source()` and
// delegates. Same shape as `verified_state.rs` in the linera_alternate
// fungible example.
//
// `AxHashMap<K, V>` (a newtype wrapper around `hashbrown::HashMap`)
// also lives here because the ghost `view_map` projection and the
// `read_balance` / `save_balance` point-op wrappers are defined
// against it; keeping all three together in one file mirrors the
// `verified_state.rs` pattern of putting the trust surface for a
// storage primitive alongside the helpers that use it.

use crate::gear_axioms::source;
use gstd::ActorId;
use hashbrown::HashMap;

pub use verus_fungible_core::TransferError;

vstd::prelude::verus! {
    /// Wrapper around `hashbrown::HashMap` so Verus sees a concrete,
    /// owned type instead of `HashMap`'s many transitive external
    /// generics (BuildHasherDefault, AHasher, Global). Methods
    /// (`read`/`save`) below are `external_body` wrappers axiomatized
    /// against a ghost view.
    #[verifier::external_body]
    #[verifier::accept_recursive_types(K)]
    #[verifier::accept_recursive_types(V)]
    pub struct AxHashMap<K, V> {
        inner: HashMap<K, V>,
    }
}

impl<K, V> Default for AxHashMap<K, V> {
    fn default() -> Self { AxHashMap { inner: HashMap::new() } }
}

vstd::prelude::verus! {
    #[cfg(verus_only)]
    use vstd::prelude::*;
    #[cfg(verus_only)]
    use vstd::map::Map as SpecMap;
    #[cfg(verus_only)]
    use crate::gear_axioms::the_sender;
    #[cfg(verus_only)]
    use verus_fungible_core::{balance_at, transfer_balances_map};

    /// Abstract view of an `AxHashMap<ActorId, u128>` as a SpecMap.
    /// Uninterpreted; only the read/save wrappers below say anything
    /// about it.
    pub uninterp spec fn view_map(m: &AxHashMap<ActorId, u128>) -> SpecMap<ActorId, u128>;

    #[verifier::external_body]
    pub fn read_balance(m: &AxHashMap<ActorId, u128>, k: &ActorId) -> (r: u128)
        ensures r == balance_at(view_map(m), *k),
    {
        m.inner.get(k).copied().unwrap_or(0)
    }

    #[verifier::external_body]
    pub fn save_balance(m: &mut AxHashMap<ActorId, u128>, k: ActorId, v: u128)
        ensures view_map(final(m)) == view_map(old(m)).insert(k, v),
    {
        m.inner.insert(k, v);
    }

    /// Verified transfer kernel: the substantive arithmetic + storage
    /// effect. Takes `sender` as an explicit parameter so it can be
    /// shared between the production path (which reads sender from
    /// `msg::source()`) and the test path (which injects sender).
    pub fn apply_transfer(
        balances: &mut AxHashMap<ActorId, u128>,
        sender:   ActorId,
        receiver: ActorId,
        amount:   u128,
    ) -> (r: Result<(), TransferError>)
        ensures
            match r {
                Ok(()) =>
                    sender != receiver
                    && view_map(final(balances))
                        == transfer_balances_map(view_map(old(balances)), sender, receiver, amount),
                Err(_) => true,
            },
    {
        if sender == receiver {
            return Err(TransferError::SelfTransfer);
        }
        let from = read_balance(balances, &sender);
        let to   = read_balance(balances, &receiver);
        match crate::core::transfer_balances(from, to, amount) {
            Ok((from_next, to_next)) => {
                save_balance(balances, sender, from_next);
                proof {
                    assert(balance_at(view_map(balances), receiver) == to);
                }
                save_balance(balances, receiver, to_next);
                Ok(())
            }
            Err(_msg) => {
                if from < amount { Err(TransferError::Insufficient) }
                else             { Err(TransferError::Overflow) }
            }
        }
    }

    /// Verified transfer entry point. Reads the sender via the axiomatized
    /// `source()`, then delegates to `apply_transfer`. This is what
    /// production `handle()` calls.
    pub fn verified_transfer(
        balances: &mut AxHashMap<ActorId, u128>,
        receiver: ActorId,
        amount:   u128,
    ) -> (r: Result<(), TransferError>)
        ensures
            match r {
                Ok(()) =>
                    the_sender() != receiver
                    && view_map(final(balances))
                        == transfer_balances_map(view_map(old(balances)), the_sender(), receiver, amount),
                Err(_) => true,
            },
    {
        let sender = source();
        apply_transfer(balances, sender, receiver, amount)
    }
}
