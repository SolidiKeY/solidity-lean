// SPDX-License-Identifier: GPL-2.0-only
pragma solidity ^0.8.0;

/// @custom:key invariant limit == 5
contract Counter {
    uint public limit = 5;
    uint public count;

    /// @custom:key ensures count == start
    constructor(uint start) {
        count = start;
    }

    /// @custom:key ensures count == \old(count) + 1
    function increment() public {
        count = count + 1;
    }
}
