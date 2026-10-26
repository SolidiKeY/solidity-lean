// SPDX-License-Identifier: GPL-3.0
pragma solidity ^0.8.0;

// Widen the inputs before arithmetic, so these are checked 256-bit sums.
contract GuardedCancellation {
    function leftUint(uint8 left, uint8 right) public pure {
        uint a = left;
        uint b = right;
        assert((a + b) - a == b);
    }
    function rightUint(uint8 left, uint8 right) public pure {
        uint a = left;
        uint b = right;
        assert((a + b) - b == a);
    }
    function leftInt(int8 left, int8 right) public pure {
        int a = left;
        int b = right;
        assert((a + b) - a == b);
    }
    function rightInt(int8 left, int8 right) public pure {
        int a = left;
        int b = right;
        assert((a + b) - b == a);
    }
    function overflowingUint() public pure returns (uint) {
        uint a = type(uint256).max;
        return (a + 1) - a;
    }
    function overflowingInt() public pure returns (int) {
        int a = type(int256).min;
        return (a + (-1)) - a;
    }
    function wrongUint(uint8 left, uint8 right) public pure {
        uint a = left;
        uint b = right;
        assert((a + b) - a == b + 1);
    }
}
