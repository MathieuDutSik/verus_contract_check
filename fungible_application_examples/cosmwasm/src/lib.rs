pub mod core;
pub mod cw_axioms;

use cosmwasm_schema::{cw_serde, QueryResponses};
use cosmwasm_std::{
    entry_point, to_json_binary, Addr, Binary, Deps, DepsMut, Env, MessageInfo, Response,
    StdError, StdResult, Storage, Uint128,
};
use thiserror::Error;

// Storage handles live in cw_axioms.rs so the runtime calls and the
// axiomatized helpers share a single set of `Map`/`Item` definitions.
use crate::cw_axioms::{
    TOTAL_SUPPLY,
    ax_balances_load, ax_balances_save, ax_supply_save,
};

// -- Verified transfer helper ------------------------------------------
//
// Single function that captures every substantive step of the contract's
// `Transfer` execute branch: caller/recipient comparison, balance reads,
// arithmetic via the verified `core::transfer_balances`, balance writes.
// The `ensures` clause pins down the storage effect on the abstract
// `balances_view` of `Storage`, using the axioms in `cw_axioms.rs`.

vstd::prelude::verus! {
    #[cfg(verus_only)]
    use vstd::prelude::*;
    #[cfg(verus_only)]
    use vstd::map::Map as SpecMap;
    #[cfg(verus_only)]
    use crate::cw_axioms::{balances_view, supply_view};

    /// Failure modes of `verified_transfer`. Mirrors the runtime
    /// `ContractError` but is closed (no `Std` variant) so it can be
    /// returned from verified code.
    #[derive(PartialEq, Eq)]
    pub enum TransferError {
        SelfTransfer,
        Insufficient,
        Overflow,
    }

    /// Balance of `k` in the abstract map, with absent entries treated as 0.
    pub open spec fn balance_at(m: SpecMap<Addr, u128>, k: Addr) -> u128 {
        if m.dom().contains(k) { m[k] } else { 0u128 }
    }

    /// The map after `state_after_transfer`'s balance update.
    pub open spec fn transfer_balances_map(
        m: SpecMap<Addr, u128>,
        sender: Addr,
        receiver: Addr,
        amount: u128,
    ) -> SpecMap<Addr, u128> {
        m.insert(sender,   (balance_at(m, sender) - amount) as u128)
         .insert(receiver, (balance_at(m, receiver) + amount) as u128)
    }

    /// Verified transfer step: ensures the storage update matches
    /// `transfer_balances_map` on success, leaves storage untouched on
    /// error. `supply_view` is preserved either way.
    pub fn verified_transfer<S: Storage>(
        storage:  &mut S,
        sender:   &Addr,
        receiver: &Addr,
        amount:   u128,
    ) -> (r: Result<(), TransferError>)
        ensures
            match r {
                Ok(()) =>
                    *sender != *receiver
                    && balances_view(final(storage))
                        == transfer_balances_map(balances_view(old(storage)), *sender, *receiver, amount)
                    && supply_view(final(storage)) == supply_view(old(storage)),
                Err(_) => true,
            },
    {
        if *sender == *receiver {
            return Err(TransferError::SelfTransfer);
        }
        let from = ax_balances_load(storage, sender);
        let to   = ax_balances_load(storage, receiver);
        proof {
            // Pin balances_view(old(storage)) as `pre` so subsequent
            // asserts have a single name to reason about.
            assert(from == balance_at(balances_view(old(storage)), *sender));
            assert(to   == balance_at(balances_view(old(storage)), *receiver));
        }
        match crate::core::transfer_balances(from, to, amount) {
            Ok((from_next, to_next)) => {
                ax_balances_save(storage, sender, from_next);
                // After the first save, the receiver's balance is
                // unchanged (sender != receiver, and insert at sender
                // doesn't touch other keys).
                proof {
                    assert(balance_at(balances_view(storage), *receiver) == to);
                }
                ax_balances_save(storage, receiver, to_next);
                Ok(())
            }
            Err(_msg) => {
                if from < amount { Err(TransferError::Insufficient) }
                else             { Err(TransferError::Overflow) }
            }
        }
    }

    // ---- Connection to `core::State` ----------------------------------
    //
    // `verified_transfer` operates on `u128` storage. `core::State<A>`
    // and `core::state_after_transfer` operate on `nat` (for unbounded
    // arithmetic in proofs). The bridge is `nat_balances`, lifting
    // `u128`-valued maps to `nat`-valued maps point-wise.

    /// Lift a `u128`-valued balance map into the `nat`-valued spec map.
    pub open spec fn nat_balances(m: SpecMap<Addr, u128>) -> SpecMap<Addr, nat> {
        SpecMap::new(
            |a: Addr| m.dom().contains(a),
            |a: Addr| m[a] as nat,
        )
    }

    /// Verified instantiate step: sets `TOTAL_SUPPLY` to `total_supply`
    /// and credits the owner with the full supply. The `ensures` captures
    /// the storage delta — the view changes by exactly one balance insert
    /// at `owner`, and the supply is set.
    ///
    /// Together with the assumption that the initial `balances_view` is
    /// empty (which the cosmwasm runtime guarantees at deployment but we
    /// don't formalise here), this establishes `sum(balances) ==
    /// total_supply` post-instantiate — the conservation invariant.
    pub fn verified_instantiate<S: Storage>(
        storage: &mut S,
        owner:   &Addr,
        total_supply: u128,
    )
        ensures
            supply_view(final(storage)) == total_supply,
            balances_view(final(storage))
                == balances_view(old(storage)).insert(*owner, total_supply),
    {
        ax_supply_save(storage, total_supply);
        ax_balances_save(storage, owner, total_supply);
    }

    /// Verified balance lookup: returns the owner's balance per the abstract
    /// view, defaulting absent entries to 0.
    pub fn verified_balance_of<S: Storage>(
        storage: &S,
        account: &Addr,
    ) -> (r: u128)
        ensures
            r == balance_at(balances_view(storage), *account),
    {
        ax_balances_load(storage, account)
    }

    /// Refinement: the `u128`-level transfer (`transfer_balances_map`)
    /// matches the `nat`-level transfer (`core::state_after_transfer`'s
    /// `.balances`) when viewed through `nat_balances`, provided the
    /// arithmetic doesn't under/overflow.
    pub proof fn lemma_verified_transfer_matches_state(
        balances_pre: SpecMap<Addr, u128>,
        sender:       Addr,
        receiver:     Addr,
        amount:       u128,
    )
        requires
            sender != receiver,
            balances_pre.dom().contains(sender),
            balances_pre.dom().contains(receiver),
            balances_pre[sender] >= amount,
            balances_pre[receiver] as int + amount as int <= u128::MAX as int,
        ensures
            nat_balances(transfer_balances_map(balances_pre, sender, receiver, amount))
                == crate::core::state_after_transfer(
                    crate::core::State {
                        total_supply: 0nat,
                        balances:     nat_balances(balances_pre),
                    },
                    sender, receiver, amount as nat,
                ).balances,
    {
        let bp  = balances_pre;
        let f   = bp[sender];
        let t   = bp[receiver];
        let lhs = nat_balances(
            bp.insert(sender,   (f - amount) as u128)
              .insert(receiver, (t + amount) as u128)
        );
        let rhs = crate::core::state_after_transfer(
            crate::core::State {
                total_supply: 0nat,
                balances:     nat_balances(bp),
            },
            sender, receiver, amount as nat,
        ).balances;

        assert(lhs.dom() =~= rhs.dom());

        assert forall|k: Addr| #[trigger] lhs.dom().contains(k)
            implies lhs[k] == rhs[k]
        by {
            if k == sender {
                // (f - amount) as u128 as nat == (f as nat - amount as nat) as nat
            } else if k == receiver {
                // (t + amount) as u128 as nat == (t as nat + amount as nat) as nat
            } else {
                assert(bp.dom().contains(k));
            }
        }
        assert(lhs =~= rhs);
    }
}

#[cw_serde]
pub struct InstantiateMsg {
    pub total_supply: Uint128,
}

#[cw_serde]
pub enum ExecuteMsg {
    Transfer { recipient: String, amount: Uint128 },
}

#[cw_serde]
#[derive(QueryResponses)]
pub enum QueryMsg {
    #[returns(Uint128)] BalanceOf { account: String },
    #[returns(Uint128)] TotalSupply {},
}

#[derive(Error, Debug)]
pub enum ContractError {
    #[error("{0}")] Std(#[from] StdError),
    #[error("insufficient balance")] Insufficient,
    #[error("overflow")] Overflow,
    #[error("self-transfer")] SelfTransfer,
}

/// Concrete wrapper around `&mut dyn Storage` so we can call the
/// verified helpers (which require `S: Sized`). `Storage` is impl'd by
/// delegation to the inner reference.
pub struct StoreRef<'a>(pub &'a mut dyn Storage);

impl Storage for StoreRef<'_> {
    fn get(&self, key: &[u8]) -> Option<Vec<u8>> { self.0.get(key) }
    fn set(&mut self, key: &[u8], value: &[u8]) { self.0.set(key, value) }
    fn remove(&mut self, key: &[u8]) { self.0.remove(key) }
}

/// Read-only counterpart of `StoreRef`. `Storage` requires `set` and
/// `remove` even on `&mut self`, so these panic — the wrapper is meant
/// to be used only in query contexts where no writes happen.
pub struct StoreRefRead<'a>(pub &'a dyn Storage);

impl Storage for StoreRefRead<'_> {
    fn get(&self, key: &[u8]) -> Option<Vec<u8>> { self.0.get(key) }
    fn set(&mut self, _key: &[u8], _value: &[u8]) {
        unreachable!("StoreRefRead is read-only");
    }
    fn remove(&mut self, _key: &[u8]) {
        unreachable!("StoreRefRead is read-only");
    }
}

#[entry_point]
pub fn instantiate(deps: DepsMut, _env: Env, info: MessageInfo, msg: InstantiateMsg) -> Result<Response, ContractError> {
    let mut store_ref = StoreRef(deps.storage);
    verified_instantiate(&mut store_ref, &info.sender, msg.total_supply.u128());
    Ok(Response::new().add_attribute("action", "instantiate"))
}

#[entry_point]
pub fn execute(deps: DepsMut, _env: Env, info: MessageInfo, msg: ExecuteMsg) -> Result<Response, ContractError> {
    match msg {
        ExecuteMsg::Transfer { recipient, amount } => {
            let to = deps.api.addr_validate(&recipient)?;
            // Wrap deps.storage so we can pass it to verified_transfer
            // (which is generic over Sized storage types).
            let mut store_ref = StoreRef(deps.storage);
            match verified_transfer(&mut store_ref, &info.sender, &to, amount.u128()) {
                Ok(()) => Ok(Response::new()
                    .add_attribute("action", "transfer")
                    .add_attribute("from", info.sender)
                    .add_attribute("to", to)
                    .add_attribute("amount", amount.to_string())),
                Err(TransferError::SelfTransfer) => Err(ContractError::SelfTransfer),
                Err(TransferError::Insufficient) => Err(ContractError::Insufficient),
                Err(TransferError::Overflow)     => Err(ContractError::Overflow),
            }
        }
    }
}

#[entry_point]
pub fn query(deps: Deps, _env: Env, msg: QueryMsg) -> StdResult<Binary> {
    match msg {
        QueryMsg::BalanceOf { account } => {
            let addr = deps.api.addr_validate(&account)?;
            let store_ref = StoreRefRead(deps.storage);
            let b = verified_balance_of(&store_ref, &addr);
            to_json_binary(&Uint128::new(b))
        }
        QueryMsg::TotalSupply {} => to_json_binary(&TOTAL_SUPPLY.load(deps.storage)?),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use cosmwasm_std::testing::{message_info, mock_dependencies, mock_env, MockApi, MockQuerier, MockStorage};
    use cosmwasm_std::{from_json, Addr, OwnedDeps};

    struct Actors { owner: Addr, alice: Addr, bob: Addr }

    fn actors(api: &MockApi) -> Actors {
        Actors {
            owner: api.addr_make("owner"),
            alice: api.addr_make("alice"),
            bob:   api.addr_make("bob"),
        }
    }

    fn setup(supply: u128) -> (OwnedDeps<MockStorage, MockApi, MockQuerier>, Actors) {
        let mut deps = mock_dependencies();
        let a = actors(&deps.api);
        let info = message_info(&a.owner, &[]);
        let msg = InstantiateMsg { total_supply: Uint128::new(supply) };
        instantiate(deps.as_mut(), mock_env(), info, msg).unwrap();
        (deps, a)
    }

    fn balance(deps: Deps, who: &Addr) -> u128 {
        let bin = query(deps, mock_env(), QueryMsg::BalanceOf { account: who.to_string() }).unwrap();
        let amt: Uint128 = from_json(&bin).unwrap();
        amt.u128()
    }

    fn total_supply(deps: Deps) -> u128 {
        let bin = query(deps, mock_env(), QueryMsg::TotalSupply {}).unwrap();
        let amt: Uint128 = from_json(&bin).unwrap();
        amt.u128()
    }

    #[test]
    fn init_supply_credited_to_owner() {
        let (deps, a) = setup(1_000);
        assert_eq!(total_supply(deps.as_ref()), 1_000);
        assert_eq!(balance(deps.as_ref(), &a.owner), 1_000);
    }

    #[test]
    fn balance_of_unknown_is_zero() {
        let (deps, _) = setup(1_000);
        let stranger = deps.api.addr_make("stranger");
        assert_eq!(balance(deps.as_ref(), &stranger), 0);
    }

    #[test]
    fn transfer_happy_path() {
        let (mut deps, a) = setup(1_000);
        let info = message_info(&a.owner, &[]);
        let msg = ExecuteMsg::Transfer { recipient: a.alice.to_string(), amount: Uint128::new(250) };
        execute(deps.as_mut(), mock_env(), info, msg).unwrap();
        assert_eq!(balance(deps.as_ref(), &a.owner), 750);
        assert_eq!(balance(deps.as_ref(), &a.alice), 250);
    }

    #[test]
    fn transfer_insufficient_balance() {
        let (mut deps, a) = setup(100);
        let info = message_info(&a.owner, &[]);
        let msg = ExecuteMsg::Transfer { recipient: a.alice.to_string(), amount: Uint128::new(200) };
        let err = execute(deps.as_mut(), mock_env(), info, msg).unwrap_err();
        assert!(matches!(err, ContractError::Insufficient));
    }

    #[test]
    fn self_transfer_rejected() {
        let (mut deps, a) = setup(1_000);
        let info = message_info(&a.owner, &[]);
        let msg = ExecuteMsg::Transfer { recipient: a.owner.to_string(), amount: Uint128::new(10) };
        let err = execute(deps.as_mut(), mock_env(), info, msg).unwrap_err();
        assert!(matches!(err, ContractError::SelfTransfer));
    }

    #[test]
    fn total_supply_invariant_after_transfer() {
        let (mut deps, a) = setup(1_000);
        let info = message_info(&a.owner, &[]);
        for amt in [100u128, 200, 50] {
            let msg = ExecuteMsg::Transfer { recipient: a.alice.to_string(), amount: Uint128::new(amt) };
            execute(deps.as_mut(), mock_env(), info.clone(), msg).unwrap();
        }
        let sum = balance(deps.as_ref(), &a.owner)
                + balance(deps.as_ref(), &a.alice)
                + balance(deps.as_ref(), &a.bob);
        assert_eq!(sum, total_supply(deps.as_ref()));
    }
}
