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
