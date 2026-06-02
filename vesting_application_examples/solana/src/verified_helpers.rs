// Verified `apply_*` kernels and end-to-end `verified_*_instruction`
// dispatchers that the Solana entry point forwards to.
//
// Two layers live here:
//
//   `apply_init_vesting` / `apply_claim`
//     Pure-data updates on a `VestingAccount` value (caller already
//     decoded the buffer). The `ensures` clauses pin down:
//       * apply_init_vesting: the initial bundle is written correctly.
//       * apply_claim: signer == beneficiary, monotonicity of `claimed`,
//         the state-level connection to `state_after_claim`.
//
//   `verified_init_instruction` / `verified_claim_instruction`
//     End-to-end dispatchers: parse positional accounts, signer check,
//     deserialise/serialise the buffer via the axiomatized
//     `read_vesting_data` / `write_vesting_data`, and call the
//     corresponding `apply_*`. Their `ensures` capture the
//     framing-free guarantees (length, signer flag); the substantive
//     properties are established by the `apply_*` ensures on the
//     locally-held `VestingAccount`.
//
// Same pattern as `verified_state.rs` in the linera_alternate fungible
// example, and as the per-chain `verified_helpers.rs` files in the
// other vesting crates.

use solana_program::{account_info::AccountInfo, pubkey::Pubkey};

use crate::solana_axioms::{
    read_is_signer, read_key, read_now_secs, read_vesting_data,
    write_vesting_data, VestingAccount, VestingError,
};
use verus_vesting_core::Params;

vstd::prelude::verus! {
    #[cfg(verus_only)]
    use vstd::prelude::*;
    #[cfg(verus_only)]
    use crate::core::{
        State as CoreState, lemma_vested_bounded, state_after_claim,
    };
    // Spec function — only available inside `verus!{}` blocks.
    #[cfg(verus_only)]
    use crate::solana_axioms::ai_signed;

    /// Initialise the vesting account. The caller is expected to have
    /// validated `vest_duration_secs > 0` and `cliff_duration_secs <=
    /// vest_duration_secs` (we *require* them).
    pub fn apply_init_vesting(
        acc:                 &mut VestingAccount,
        beneficiary:         Pubkey,
        start_secs:          u64,
        cliff_duration_secs: u64,
        vest_duration_secs:  u64,
        total:               u128,
    ) -> (r: Result<(), VestingError>)
        requires
            vest_duration_secs > 0,
            cliff_duration_secs <= vest_duration_secs,
        ensures
            match r {
                Ok(()) =>
                    !old(acc).initialized
                    && final(acc).initialized
                    && final(acc).beneficiary         == beneficiary
                    && final(acc).start_secs          == start_secs
                    && final(acc).cliff_duration_secs == cliff_duration_secs
                    && final(acc).vest_duration_secs  == vest_duration_secs
                    && final(acc).total               == total
                    && final(acc).claimed             == 0u128,
                Err(_) => true,
            },
    {
        if acc.initialized { return Err(VestingError::AlreadyInitialized); }
        acc.initialized         = true;
        acc.beneficiary         = beneficiary;
        acc.start_secs          = start_secs;
        acc.cliff_duration_secs = cliff_duration_secs;
        acc.vest_duration_secs  = vest_duration_secs;
        acc.total               = total;
        acc.claimed             = 0;
        Ok(())
    }

    /// Verified claim step. Updates the account's `claimed` field with
    /// the schedule's claimable amount at `now_secs`; rejects if the
    /// signer's key isn't the registered beneficiary.
    ///
    /// `ensures` (success path):
    ///   - the account was initialised.
    ///   - `signer_key == acc.beneficiary`.
    ///   - the immutable schedule fields are preserved.
    ///   - `final(acc).claimed >= old(acc).claimed` (monotonic).
    ///   - `returned amount == final.claimed - old.claimed`.
    ///   - state-level connection: `final.claimed == state_after_claim
    ///     (CoreState { beneficiary, params, claimed: old.claimed },
    ///      now_secs).claimed`.
    pub fn apply_claim(
        acc:        &mut VestingAccount,
        signer_key: Pubkey,
        now_secs:   u64,
    ) -> (r: Result<u128, VestingError>)
        requires
            old(acc).initialized,
            old(acc).vest_duration_secs > 0,
            old(acc).cliff_duration_secs <= old(acc).vest_duration_secs,
            (old(acc).claimed as nat) <= (old(acc).total as nat),
        ensures
            // Immutable fields preserved.
            final(acc).initialized         == old(acc).initialized,
            final(acc).beneficiary         == old(acc).beneficiary,
            final(acc).start_secs          == old(acc).start_secs,
            final(acc).cliff_duration_secs == old(acc).cliff_duration_secs,
            final(acc).vest_duration_secs  == old(acc).vest_duration_secs,
            final(acc).total               == old(acc).total,
            // Monotonic claimed.
            final(acc).claimed >= old(acc).claimed,
            match r {
                Ok(amount) => {
                    &&& old(acc).initialized
                    &&& signer_key == old(acc).beneficiary
                    &&& amount as int == (final(acc).claimed as int) - (old(acc).claimed as int)
                    &&& final(acc).claimed as int
                        == state_after_claim::<Pubkey>(
                                CoreState {
                                    beneficiary: old(acc).beneficiary,
                                    params:      Params {
                                        start:          old(acc).start_secs,
                                        cliff_duration: old(acc).cliff_duration_secs,
                                        vest_duration:  old(acc).vest_duration_secs,
                                        total:          old(acc).total,
                                    },
                                    claimed:     old(acc).claimed,
                                },
                                now_secs,
                           ).claimed as int
                }
                Err(_) => true,
            },
    {
        if !acc.initialized { return Err(VestingError::NotInitialized); }
        if signer_key != acc.beneficiary { return Err(VestingError::Unauthorized); }
        let params = Params {
            start:          acc.start_secs,
            cliff_duration: acc.cliff_duration_secs,
            vest_duration:  acc.vest_duration_secs,
            total:          acc.total,
        };
        let amount = match verus_vesting_core::compute_claim(&params, now_secs, acc.claimed) {
            Ok(a)  => a,
            Err(_) => return Err(VestingError::ArithOverflow),
        };
        proof {
            lemma_vested_bounded(params, now_secs);
        }
        if amount > 0 {
            acc.claimed = acc.claimed + amount;
        }
        Ok(amount)
    }

    // -- End-to-end verified instructions ----------------------------------

    /// End-to-end Init: parse positional accounts, signer check, init
    /// args validation, deserialise the (empty) vesting account, call
    /// `apply_init_vesting`, write back.
    ///
    /// Positional convention:
    ///   accounts[0]: payer (must be a signer)
    ///   accounts[1]: vesting account to initialise (mutable buffer)
    pub fn verified_init_instruction<'a>(
        accounts:            &'a [AccountInfo<'a>],
        beneficiary:         Pubkey,
        start_secs:          u64,
        cliff_duration_secs: u64,
        vest_duration_secs:  u64,
        total:               u128,
    ) -> (r: Result<(), VestingError>)
        ensures
            match r {
                Ok(()) => accounts.len() >= 2 && ai_signed(&accounts[0]),
                Err(_) => true,
            },
    {
        if accounts.len() < 2 { return Err(VestingError::InvalidArgument); }
        let payer   = &accounts[0];
        let vesting = &accounts[1];
        if !read_is_signer(payer) { return Err(VestingError::MissingSignature); }

        // Init-arg validation (matches apply_init_vesting's requires).
        if vest_duration_secs == 0 { return Err(VestingError::ZeroVestDuration); }
        if cliff_duration_secs > vest_duration_secs { return Err(VestingError::CliffTooLong); }

        let mut acc = match read_vesting_data(vesting) {
            Ok(d)  => d,
            Err(e) => return Err(e),
        };
        match apply_init_vesting(
            &mut acc, beneficiary, start_secs, cliff_duration_secs,
            vest_duration_secs, total,
        ) {
            Ok(())  => {}
            Err(e)  => return Err(e),
        }
        match write_vesting_data(vesting, &acc) {
            Ok(())  => Ok(()),
            Err(e)  => Err(e),
        }
    }

    /// End-to-end Claim: parse positional accounts, signer check, fetch
    /// time from Clock sysvar, call `apply_claim`, write back.
    ///
    /// Positional convention:
    ///   accounts[0]: beneficiary (must be a signer; key checked
    ///                inside apply_claim against acc.beneficiary)
    ///   accounts[1]: vesting account (mutable buffer)
    ///
    /// `ensures` (success path):
    ///   - accounts.len() >= 2 and accounts[0] is a signer.
    ///   - (The substantive properties — auth, monotonicity, schedule
    ///     correctness — are pinned by `apply_claim`'s ensures on the
    ///     local `acc` value; we don't restate them at the dispatch
    ///     level for the same framing reason as the fungible Solana
    ///     contract, see TODO.md.)
    pub fn verified_claim_instruction<'a>(
        accounts: &'a [AccountInfo<'a>],
    ) -> (r: Result<u128, VestingError>)
        ensures
            match r {
                Ok(_)  => accounts.len() >= 2 && ai_signed(&accounts[0]),
                Err(_) => true,
            },
    {
        if accounts.len() < 2 { return Err(VestingError::InvalidArgument); }
        let signer  = &accounts[0];
        let vesting = &accounts[1];
        if !read_is_signer(signer) { return Err(VestingError::MissingSignature); }
        let signer_key = read_key(signer);

        let mut acc = match read_vesting_data(vesting) {
            Ok(d)  => d,
            Err(e) => return Err(e),
        };
        // The verified-init path establishes `acc.initialized` and the
        // schedule's well-formedness; we must restate them at runtime
        // because Verus can't carry that across the Borsh read.
        if !acc.initialized { return Err(VestingError::NotInitialized); }
        if acc.vest_duration_secs == 0 { return Err(VestingError::ZeroVestDuration); }
        if acc.cliff_duration_secs > acc.vest_duration_secs { return Err(VestingError::CliffTooLong); }
        if acc.claimed > acc.total { return Err(VestingError::InvalidArgument); }

        let now_secs = read_now_secs();
        let amount = match apply_claim(&mut acc, signer_key, now_secs) {
            Ok(a)  => a,
            Err(e) => return Err(e),
        };
        match write_vesting_data(vesting, &acc) {
            Ok(())  => Ok(amount),
            Err(e)  => Err(e),
        }
    }
}
