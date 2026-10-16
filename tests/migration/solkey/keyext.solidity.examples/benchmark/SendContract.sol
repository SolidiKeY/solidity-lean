// Source: https://raw.githubusercontent.com/ethereum/solidity/v0.8.30/docs/common-patterns.rst
// Changes: the custom error is dropped, `revert NotEnoughEther()` becomes `revert()`.
// SPDX-License-Identifier: GPL-3.0
pragma solidity ^0.8.4;

/// @custom:key invariant mostSent >= 0
contract SendContract {
    address payable public richest;
    uint public mostSent;

    /// The amount of Ether sent was not higher than
    /// the currently highest amount.

    /// @custom:key ensures richest == msg.sender && mostSent == msg.value
    constructor() payable {
        richest = payable(msg.sender);
        mostSent = msg.value;
    }

    /// @custom:key requires richest != address(this)
    /// @custom:key ensures \old(mostSent) < msg.value
    /// @custom:key ensures richest == msg.sender && mostSent == msg.value
    /// @custom:key ensures \old(richest) != msg.sender -> net(\old(richest)) == \old(net(richest)) - msg.value
    function becomeRichest() public payable {
        if (msg.value <= mostSent) revert();
        // This line can cause problems (explained below).
        richest.transfer(msg.value);
        richest = payable(msg.sender);
        mostSent = msg.value;
    }
}
