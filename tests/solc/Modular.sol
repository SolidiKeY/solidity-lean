// SPDX-License-Identifier: MIT
pragma solidity ^0.8.34;

contract Modular {
    function bad() internal pure returns (uint) { assert(false); return 1; }

    function wide() public pure {
        assert(addmod(type(uint).max, 1, 3) == 1);
        assert(mulmod(2 ** 255, 2, 3) == 1);
    }

    /// @custom:key box
    function zeroBeforeBad() public pure {
        uint k = 0;
        uint r = addmod(bad(), 2, k);
    }

    /// @custom:key box
    function positiveBad() public pure {
        uint k = 3;
        uint r = mulmod(1, bad(), k);
    }

    function ordered() public pure {
        uint i = 3;
        uint r = addmod(i++, i++, i++);
        assert(i == 6);
        assert(r == 0);
    }

    function capturedRead() public pure {
        uint i = 3;
        uint r = addmod(i++, 2, i);
        assert(i == 4);
        assert(r == 2);
    }
}

contract ModularShadow {
    function addmod(uint a, uint b, uint k) internal pure returns (uint) { return 99; }

    function usesDeclaredFunction() public pure {
        assert(addmod(1, 2, 3) == 99);
    }
}
