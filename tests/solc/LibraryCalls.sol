// SPDX-License-Identifier: GPL-3.0
pragma solidity ^0.8.0;
uint constant FILE_BASE = 4;
function doubleValue(uint x) pure returns (uint) { return 2 * x; }
/// @custom:key ensures \result == 0
function recursiveValue(uint x) pure returns (uint) { return recursiveValue(x); }
library LibA {
    uint constant UNIT = 10;
    function bump(uint x) internal pure returns (uint) { return x + UNIT; }
    function digits(uint self, uint left, uint right) internal pure returns (uint) {
        return self * 100 + left * 10 + right;
    }
    function composed(uint x) internal pure returns (uint) { return LibA.bump(x) + doubleValue(1); }
    function pair(uint x) internal pure returns (uint, uint) { return (x, x + 1); }
    /// @custom:key box
    function ownCalls() public pure { assert(LibA.composed(5) == 17); }
}
library LibB {
    function bump(uint x) internal pure returns (uint) { return x + 20; }
}
contract LibraryCalls {
    using LibA for uint;
    using {doubleValue} for uint;
    function bump(uint x) internal pure returns (uint) { return x + 30; }
    /// @custom:key box
    function declarationsStayDistinct() public pure {
        assert(LibA.bump(5) == 15);
        assert(LibB.bump(5) == 25);
        assert(bump(5) == 35);
        assert(doubleValue(FILE_BASE) == 8);
        assert(LibA.composed(5) == 17);
    }
    /// @custom:key box
    function attachedAndNamed() public pure {
        uint v = 5;
        assert(v.bump() == 15);
        assert(v.doubleValue() == 10);
        assert(v.digits({right: 3, left: 2}) == 523);
        assert(LibA.digits({right: 3, self: 5, left: 2}) == 523);
    }
    /// @custom:key box
    function receiverOnce() public pure {
        uint v = 5;
        uint n = (v++).bump();
        assert(n == 15 && v == 6);
    }
    /// @custom:key box
    function tupleCalls() public pure {
        (uint a, uint b) = LibA.pair(5);
        assert(a == 5 && b == 6);
        (a, b) = a.pair();
        assert(a == 5 && b == 6);
    }
    /// @custom:key box
    function falsePost() public pure { assert(LibB.bump(5) == 15); }
    function recursionGap() public pure { assert(recursiveValue(0) == 0); }
}
