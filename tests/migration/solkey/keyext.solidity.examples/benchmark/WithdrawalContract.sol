// Source: https://raw.githubusercontent.com/ethereum/solidity/v0.8.30/docs/common-patterns.rst
// Changes: the custom error is dropped, `revert NotEnoughEther()` becomes `revert()`.
// SPDX-License-Identifier: GPL-3.0
pragma solidity ^0.8.4;

/// @custom:key invariant mostSent >= 0
/// @custom:key invariant \forall address a; pendingWithdrawals[a] >= 0
contract WithdrawalContract {
    address public richest;
    uint public mostSent;

    mapping(address => uint) pendingWithdrawals;

    /// The amount of Ether sent was not higher than
    /// the currently highest amount.

    /// @custom:key ensures richest == msg.sender && mostSent == msg.value
    constructor() payable {
        richest = msg.sender;
        mostSent = msg.value;
    }

    /// @custom:key ensures \old(mostSent) < msg.value
    /// @custom:key ensures richest == msg.sender && mostSent == msg.value
    /// @custom:key ensures pendingWithdrawals[\old(richest)] == \old(pendingWithdrawals[richest]) + msg.value
    /// @custom:key ensures \forall address a; a != \old(richest) -> pendingWithdrawals[a] == \old(pendingWithdrawals[a])
    function becomeRichest() public payable {
        if (msg.value <= mostSent) revert();
        pendingWithdrawals[richest] += msg.value;
        richest = msg.sender;
        mostSent = msg.value;
    }

    /// @custom:key ensures pendingWithdrawals[msg.sender] == 0
    /// @custom:key ensures net(msg.sender) == \old(net(msg.sender)) - \old(pendingWithdrawals[msg.sender])
    /// @custom:key ensures \forall address a; a != msg.sender -> pendingWithdrawals[a] == \old(pendingWithdrawals[a])
    function withdraw() public {
        uint amount = pendingWithdrawals[msg.sender];
        // Remember to zero the pending refund before
        // sending to prevent reentrancy attacks
        pendingWithdrawals[msg.sender] = 0;
        payable(msg.sender).transfer(amount);
    }
}
