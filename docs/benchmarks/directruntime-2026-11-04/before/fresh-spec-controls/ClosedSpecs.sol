// SPDX-License-Identifier: MIT
pragma solidity ^0.8.34;
contract ClosedSpecs {
    uint value;
    /// @custom:key ensures \result >= x
    function maximum(uint x, uint y) public pure returns (uint result) {
        if (x >= y) return x;
        return y;
    }
    /// @custom:key ensures \result > x
    function falseMaximum(uint x, uint y) public pure returns (uint result) {
        if (x >= y) return x;
        return y;
    }
    /// @custom:key ensures value >= x
    function storeMaximum(uint x, uint y) public {
        uint r;
        if (x >= y) r = x; else r = y;
        value = r;
    }
    /// @custom:key ensures \result >= x
    function twoChoices(uint x, uint y, uint z) public pure returns (uint result) {
        result = x;
        if (y > result) result = y;
        if (z > result) result = z;
    }
    /// @custom:key ensures \result == 1
    function constantOne() public pure returns (uint result) { return 1; }
    /// @custom:key ensures \result == 1
    function falseConstant() public pure returns (uint result) { return 2; }
    /// @custom:key ensures value == x
    function store(uint x) public { value = x; }
    /// @custom:key ensures value == 1
    function falseStore() public { value = 2; }
}
