// SPDX-License-Identifier: GPL-3.0
pragma solidity ^0.8.0;

contract Cli {
    uint public count;

    /// @custom:key box
    function passes(uint x) public pure { require(x == 7); assert(x == 7); }

    /// @custom:key box
    function fails() public pure { assert(false); }

    /// @custom:key ensures true
    function specified() public pure {}

    function inc(uint amount) public returns (uint) {
        count += amount;
        return count;
    }

    function overloaded(uint256 x) public pure returns (uint256) { return x; }
    function overloaded(bool x) public pure returns (bool) { return x; }

    function forbidden() public pure { assembly { mstore(0, 0) } }
}
