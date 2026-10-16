// Source: https://raw.githubusercontent.com/ethereum/solidity/v0.8.30/docs/introduction-to-smart-contracts.rst
// Changes: the event and the custom error are dropped, `require(c, Err(..))` becomes
// `require(c)`, the emit is dropped.
// SPDX-License-Identifier: GPL-3.0
pragma solidity ^0.8.26;

// This will only compile via IR
contract Coin {
    // The keyword "public" makes variables
    // accessible from other contracts
    address public minter;
    mapping(address => uint) public balances;

    // Events allow clients to react to specific
    // contract changes you declare

    // Constructor code is only run when the contract
    // is created
    /// @custom:key ensures minter == msg.sender
    constructor() {
        minter = msg.sender;
    }

    // Sends an amount of newly created coins to an address
    // Can only be called by the contract creator
    /// @custom:key requires amount >= 0
    /// @custom:key ensures \old(minter) == msg.sender && minter == \old(minter)
    /// @custom:key ensures balances[receiver] == \old(balances[receiver]) + amount
    /// @custom:key ensures \forall address a; a != receiver -> balances[a] == \old(balances[a])
    function mint(address receiver, uint amount) public {
        require(msg.sender == minter);
        balances[receiver] += amount;
    }

    // Errors allow you to provide information about
    // why an operation failed. They are returned
    // to the caller of the function.

    // Sends an amount of existing coins
    // from any caller to an address
    /// @custom:key requires amount >= 0
    /// @custom:key ensures \old(balances[msg.sender]) >= amount
    /// @custom:key ensures msg.sender != receiver -> balances[msg.sender] == \old(balances[msg.sender]) - amount && balances[receiver] == \old(balances[receiver]) + amount
    /// @custom:key ensures msg.sender == receiver -> balances[msg.sender] == \old(balances[msg.sender])
    /// @custom:key ensures \forall address a; a != msg.sender && a != receiver -> balances[a] == \old(balances[a])
    function send(address receiver, uint amount) public {
        require(amount <= balances[msg.sender]);
        balances[msg.sender] -= amount;
        balances[receiver] += amount;
    }
}
