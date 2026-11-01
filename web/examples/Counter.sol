// SPDX-License-Identifier: MIT
pragma solidity ^0.8.34;

contract Counter {
    uint256 public count;

    /// @custom:key ensures count == \old(count) + 1
    function increment() public {
        count = count + 1;
    }

    /// @custom:key ensures count == 0
    function reset() public {
        count = 0;
    }

    /// @custom:key ensures \result == 1
    function one() public pure returns (uint256 result) {
        return 1;
    }

    /// @custom:key ensures \result == 1
    function openGoal() public pure returns (uint256 result) {
        return 2;
    }
}
