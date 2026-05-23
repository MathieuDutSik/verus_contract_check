use cosmwasm_schema::{cw_serde, QueryResponses};
use cosmwasm_std::{
    entry_point, to_json_binary, Addr, Binary, Deps, DepsMut, Env, MessageInfo, Response,
    StdError, StdResult, Uint128,
};
use cw_storage_plus::{Item, Map};
use thiserror::Error;

const TOTAL_SUPPLY: Item<Uint128> = Item::new("total_supply");
const BALANCES: Map<&Addr, Uint128> = Map::new("balances");

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

#[entry_point]
pub fn instantiate(deps: DepsMut, _env: Env, info: MessageInfo, msg: InstantiateMsg) -> Result<Response, ContractError> {
    TOTAL_SUPPLY.save(deps.storage, &msg.total_supply)?;
    BALANCES.save(deps.storage, &info.sender, &msg.total_supply)?;
    Ok(Response::new().add_attribute("action", "instantiate"))
}

#[entry_point]
pub fn execute(deps: DepsMut, _env: Env, info: MessageInfo, msg: ExecuteMsg) -> Result<Response, ContractError> {
    match msg {
        ExecuteMsg::Transfer { recipient, amount } => {
            let to = deps.api.addr_validate(&recipient)?;
            if to == info.sender { return Err(ContractError::SelfTransfer); }
            let from_balance = BALANCES.may_load(deps.storage, &info.sender)?.unwrap_or_default();
            let from_next = from_balance.checked_sub(amount).map_err(|_| ContractError::Insufficient)?;
            let to_balance = BALANCES.may_load(deps.storage, &to)?.unwrap_or_default();
            let to_next = to_balance.checked_add(amount).map_err(|_| ContractError::Overflow)?;
            BALANCES.save(deps.storage, &info.sender, &from_next)?;
            BALANCES.save(deps.storage, &to, &to_next)?;
            Ok(Response::new()
                .add_attribute("action", "transfer")
                .add_attribute("from", info.sender)
                .add_attribute("to", to)
                .add_attribute("amount", amount.to_string()))
        }
    }
}

#[entry_point]
pub fn query(deps: Deps, _env: Env, msg: QueryMsg) -> StdResult<Binary> {
    match msg {
        QueryMsg::BalanceOf { account } => {
            let addr = deps.api.addr_validate(&account)?;
            let b = BALANCES.may_load(deps.storage, &addr)?.unwrap_or_default();
            to_json_binary(&b)
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
