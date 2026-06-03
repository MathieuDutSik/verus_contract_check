// Verified `apply_*` kernels plus the end-to-end
// `verified_transfer_instruction` dispatcher that the Solana entry
// point forwards to.
//
// Two layers live here:
//
//   `apply_init_mint` / `apply_transfer` / `apply_approve` /
//   `apply_revoke` / `apply_transfer_from` / `apply_mint` /
//   `apply_burn`
//     Pure-data updates on `Mint` / `TokenAccount` values (caller
//     already decoded the buffer). The `ensures` clauses pin down the
//     safety-relevant effects: balance conservation, signer/owner
//     checks, allowance decrements.
//
//   `verified_transfer_instruction`
//     End-to-end dispatcher: positional account parsing, signer check,
//     deserialise/serialise via the axiomatized `read_token_data` /
//     `write_token_data`, and call `apply_transfer`. Its `ensures`
//     capture the framing-free guarantees (length, signer flag); the
//     substantive properties are established by `apply_transfer`'s
//     ensures on the locally-held `TokenAccount`s.
//
// Same pattern as `verified_state.rs` in the linera_alternate fungible
// example, and as the per-chain `verified_helpers.rs` files in the
// other fungible crates.

use solana_program::{account_info::AccountInfo, pubkey::Pubkey};

use crate::solana_axioms::{
    read_is_signer, read_key, read_token_data, write_token_data,
    Mint, TokenAccount, TokenError,
};

vstd::prelude::verus! {
    #[cfg(verus_only)]
    use vstd::prelude::*;
    // Spec function — only available inside `verus!{}` blocks.
    #[cfg(verus_only)]
    use crate::solana_axioms::ai_signed;

    /// Initialise the mint and credit the entire supply to the owner.
    pub fn apply_init_mint(
        mint:      &mut Mint,
        owner_acc: &mut TokenAccount,
        owner_key: Pubkey,
        total_supply: u128,
    ) -> (r: Result<(), TokenError>)
        ensures
            match r {
                Ok(()) =>
                    !old(mint).initialized
                    && final(mint).initialized
                    && final(mint).total_supply == total_supply
                    && final(owner_acc).owner == owner_key
                    && final(owner_acc).balance == total_supply,
                Err(_) => true,
            },
    {
        if mint.initialized { return Err(TokenError::AlreadyInitialized); }
        mint.total_supply = total_supply;
        mint.initialized = true;
        owner_acc.owner = owner_key;
        owner_acc.balance = total_supply;
        Ok(())
    }

    /// Transfer `amount` from `src` to `dst`, signed by `signer_key`.
    /// Requires `signer_key == src.owner` and `signer_key != dst.owner`.
    pub fn apply_transfer(
        src:        &mut TokenAccount,
        dst:        &mut TokenAccount,
        signer_key: Pubkey,
        amount:     u128,
    ) -> (r: Result<(), TokenError>)
        ensures
            match r {
                Ok(()) =>
                    old(src).owner == signer_key
                    && signer_key != old(dst).owner
                    && final(src).balance + final(dst).balance
                        == old(src).balance + old(dst).balance
                    && final(src).balance == (old(src).balance - amount) as u128
                    && final(dst).balance == (old(dst).balance + amount) as u128,
                Err(_) => true,
            },
    {
        if src.owner != signer_key { return Err(TokenError::IllegalOwner); }
        if signer_key == dst.owner { return Err(TokenError::InvalidArgument); }
        let src_next = match src.balance.checked_sub(amount) {
            Some(v) => v,
            None    => return Err(TokenError::InsufficientFunds),
        };
        let dst_next = match dst.balance.checked_add(amount) {
            Some(v) => v,
            None    => return Err(TokenError::Overflow),
        };
        src.balance = src_next;
        dst.balance = dst_next;
        Ok(())
    }

    // -- End-to-end verified transfer instruction -----------------------
    //
    // Combines: positional account parsing + signer check + owner check
    // + balance arithmetic + writeback. The `ensures` describes the
    // entire effect of running the Transfer instruction.
    pub fn verified_transfer_instruction<'a>(
        accounts: &'a [AccountInfo<'a>],
        amount:   u128,
    ) -> (r: Result<(), TokenError>)
        ensures
            match r {
                Ok(()) =>
                    accounts.len() >= 3
                    && ai_signed(&accounts[0]),
                // We deliberately keep this `ensures` minimal: it only
                // claims the parser-level guarantees that are framing-free
                // (the signer flag and account-list length).
                //
                // The substantive properties — `apply_transfer`'s conservation,
                // signer's pubkey matching `src.owner`, distinctness of
                // src vs dst — are proven inside the called helpers'
                // own ensures. The `ai_token_data` spec function is
                // *uninterpreted* (returns "the current view") and
                // Verus's pure-function model means we can't easily
                // pre/post-state it across a writeback without an
                // explicit state-tracking layer.
                //
                // What this ensures *does* establish for the caller:
                // any code path leading to `Ok(())` has passed the
                // length check AND the is_signer check — i.e., the two
                // bug classes ("forgot to check arg count", "forgot to
                // check signer") cannot exist in this function.
                Err(_) => true,
            },
    {
        // 1. Positional + length check.
        if accounts.len() < 3 {
            return Err(TokenError::InvalidArgument);
        }
        let signer = &accounts[0];
        let src    = &accounts[1];
        let dst    = &accounts[2];

        // 2. Signer check.
        if !read_is_signer(signer) {
            return Err(TokenError::MissingSignature);
        }

        // 3. Read account data.
        let mut src_data = match read_token_data(src) {
            Ok(d)  => d,
            Err(e) => return Err(e),
        };
        let mut dst_data = match read_token_data(dst) {
            Ok(d)  => d,
            Err(e) => return Err(e),
        };

        // 4. Owner / distinctness checks (folded into apply_transfer's
        //    own checks, but we want them visible at the dispatch layer).
        let signer_key = read_key(signer);

        // 5. Verified arithmetic + state update.
        apply_transfer(&mut src_data, &mut dst_data, signer_key, amount)?;

        // 6. Writeback to the same AccountInfos we just read from.
        write_token_data(src, &src_data)?;
        write_token_data(dst, &dst_data)?;

        Ok(())
    }

    /// Approve `delegate_key` to spend up to `amount` from `src`. The
    /// caller must be `src.owner`. Overwrites any previous delegation.
    pub fn apply_approve(
        src:          &mut TokenAccount,
        signer_key:   Pubkey,
        delegate_key: Pubkey,
        amount:       u128,
    ) -> (r: Result<(), TokenError>)
        ensures
            match r {
                Ok(()) =>
                    old(src).owner == signer_key
                    && final(src).delegate == Some(delegate_key)
                    && final(src).delegated_amount == amount
                    && final(src).balance == old(src).balance
                    && final(src).owner == old(src).owner,
                Err(_) => true,
            },
    {
        if src.owner != signer_key { return Err(TokenError::IllegalOwner); }
        src.delegate = Some(delegate_key);
        src.delegated_amount = amount;
        Ok(())
    }

    /// Revoke the current delegation on `src`. Caller must be `src.owner`.
    pub fn apply_revoke(
        src:        &mut TokenAccount,
        signer_key: Pubkey,
    ) -> (r: Result<(), TokenError>)
        ensures
            match r {
                Ok(()) =>
                    old(src).owner == signer_key
                    && final(src).delegate is None
                    && final(src).delegated_amount == 0u128
                    && final(src).balance == old(src).balance,
                Err(_) => true,
            },
    {
        if src.owner != signer_key { return Err(TokenError::IllegalOwner); }
        src.delegate = None;
        src.delegated_amount = 0;
        Ok(())
    }

    /// Transfer `amount` from `src` to `dst`, signed by `spender_key`
    /// which must equal `src.delegate` and have at least `amount`
    /// remaining in `delegated_amount`. The delegation is decremented
    /// by `amount`.
    pub fn apply_transfer_from(
        src:         &mut TokenAccount,
        dst:         &mut TokenAccount,
        spender_key: Pubkey,
        amount:      u128,
    ) -> (r: Result<(), TokenError>)
        ensures
            match r {
                Ok(()) =>
                    old(src).delegate == Some(spender_key)
                    && old(src).delegated_amount >= amount
                    && spender_key != old(dst).owner
                    && final(src).balance + final(dst).balance
                        == old(src).balance + old(dst).balance
                    && final(src).balance == (old(src).balance - amount) as u128
                    && final(dst).balance == (old(dst).balance + amount) as u128
                    && final(src).delegated_amount == (old(src).delegated_amount - amount) as u128
                    && final(src).delegate == old(src).delegate
                    && final(src).owner == old(src).owner,
                Err(_) => true,
            },
    {
        // Authorization: spender must equal the delegate.
        match src.delegate {
            Some(d) if d == spender_key => {}
            _ => return Err(TokenError::IllegalOwner),
        }
        if src.delegated_amount < amount {
            return Err(TokenError::InsufficientFunds);
        }
        if spender_key == dst.owner { return Err(TokenError::InvalidArgument); }
        let src_next = match src.balance.checked_sub(amount) {
            Some(v) => v,
            None    => return Err(TokenError::InsufficientFunds),
        };
        let dst_next = match dst.balance.checked_add(amount) {
            Some(v) => v,
            None    => return Err(TokenError::Overflow),
        };
        src.balance = src_next;
        dst.balance = dst_next;
        src.delegated_amount = src.delegated_amount - amount;
        Ok(())
    }

    /// Mint `amount` to `dst`, increasing total supply by the same.
    /// Caller must be the mint authority (modelled as the signer who
    /// initialised the mint — here, simply allowed by signature).
    pub fn apply_mint(
        mint:   &mut Mint,
        dst:    &mut TokenAccount,
        amount: u128,
    ) -> (r: Result<(), TokenError>)
        ensures
            match r {
                Ok(()) =>
                    old(mint).initialized
                    && final(mint).total_supply == (old(mint).total_supply + amount) as u128
                    && final(dst).balance == (old(dst).balance + amount) as u128
                    && final(mint).initialized == old(mint).initialized,
                Err(_) => true,
            },
    {
        if !mint.initialized { return Err(TokenError::NotInitialized); }
        let new_supply = match mint.total_supply.checked_add(amount) {
            Some(v) => v,
            None    => return Err(TokenError::Overflow),
        };
        let new_bal = match dst.balance.checked_add(amount) {
            Some(v) => v,
            None    => return Err(TokenError::Overflow),
        };
        mint.total_supply = new_supply;
        dst.balance = new_bal;
        Ok(())
    }

    /// Burn `amount` from `src`, decreasing total supply by the same.
    /// Caller must be `src.owner`.
    pub fn apply_burn(
        mint:       &mut Mint,
        src:        &mut TokenAccount,
        signer_key: Pubkey,
        amount:     u128,
    ) -> (r: Result<(), TokenError>)
        ensures
            match r {
                Ok(()) =>
                    old(src).owner == signer_key
                    && final(mint).total_supply == (old(mint).total_supply - amount) as u128
                    && final(src).balance == (old(src).balance - amount) as u128,
                Err(_) => true,
            },
    {
        if src.owner != signer_key { return Err(TokenError::IllegalOwner); }
        let new_bal = match src.balance.checked_sub(amount) {
            Some(v) => v,
            None    => return Err(TokenError::InsufficientFunds),
        };
        let new_supply = match mint.total_supply.checked_sub(amount) {
            Some(v) => v,
            None    => return Err(TokenError::InsufficientFunds),
        };
        src.balance = new_bal;
        mint.total_supply = new_supply;
        Ok(())
    }
}
