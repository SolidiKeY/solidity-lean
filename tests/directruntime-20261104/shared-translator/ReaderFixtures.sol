// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;
contract ReaderFixtures {
    uint256 public count;
    uint256[] public values;
    uint256[3] public fixedValues;
    mapping(uint256 => bool) public flags;
    function scalar(uint256 x, int256 y, bool b) public returns (uint256) {
        uint256 z = b ? x + 1 : x;
        if (b) { count = z; } else { count += 1; }
        require(z >= x);
        assert(y == y);
        unchecked { z++; z--; }
        return z;
    }
    function arrays(uint256 i) public {
        values.push(i);
        if (values.length > 0) { values[i] = fixedValues[0]; }
        flags[i] = true;
        delete flags[i];
        values.pop();
    }
    function loops(uint256 n) public {
        for (uint256 i = 0; i < n; i++) {
            if (i == 1) continue;
            if (i == 2) break;
            count = i;
        }
        while (count > 0) { count--; }
    }
    /// @custom:key requires x >= 0
    /// @custom:key ensures \result >= x
    function specified(uint256 x) public pure returns (uint256) { return x; }
    function unsupportedMemory(uint256[] memory x) public pure returns (uint256) { return x.length; }
    function unsupportedTuple(uint256 x) public pure returns (uint256, uint256) { return (x, x); }
    function unsupportedDoWhile() public { do { count++; } while (count < 1); }
    function overloaded(uint256 x) public pure returns (uint256) { return x; }
    function overloaded(bool x) public pure returns (bool) { return x; }
}
