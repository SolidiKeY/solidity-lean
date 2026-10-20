// SPDX-License-Identifier: GPL-2.0-only
pragma solidity ^0.8.0;

contract SolcArithmeticOpen {
    uint[] array;
    mapping(uint => uint) map;

    modifier addUnchecked(uint a, uint b) {
        unchecked {
            a + b;
        }
        _;
    }

    function addUnchecked16(uint16 a, uint16 b) internal pure returns (uint16) {
        unchecked {
            return a + b;
        }
    }

    function add16(uint16 a, uint16 b) internal pure returns (uint16) {
        return a + b;
    }





    // open: design-limitation: unbounded integers, uint16 0xffff + 0x100 does not wrap to 0xff
    /// solc: semanticTests/arithmetics/unchecked_called_by_checked.sol
    /// @custom:key box
    function uncheckedCalledByCheckedWraps(uint16 a) public pure {
        require(a == 0xffff);
        uint16 r = addUnchecked16(a, 0x100) + 0x100;
        assert(r == 511);
    }

    // open: design-limitation: unbounded integers, the unchecked uint16 sum 0x10000 does not wrap to 0
    /// solc: semanticTests/arithmetics/checked_called_by_unchecked.sol
    /// @custom:key box
    function checkedCalledByUncheckedWraps(uint16 a, uint16 b, uint16 c) public pure {
        require(a == 0xe000 && b == 0x1000 && c == 0x1000);
        uint16 r;
        unchecked {
            r = add16(a, b) + c;
        }
        assert(r == 0);
    }

    // open: design-limitation: unbounded integers, 2**256 - 1 + 1 does not wrap to 0
    /// solc: semanticTests/arithmetics/block_inside_unchecked.sol
    function blockInsideUnchecked() public pure {
        uint y;
        unchecked {{
            uint max = 2**256 - 1;
            uint x = max + 1;
            y = x;
        }}
        assert(y == 0);
    }

    // open: design-limitation: unbounded integers, ++x on 2**256 - 1 does not wrap to 0
    /// solc: smtCheckerTests/unchecked/inc_dec.sol
    function uncheckedIncrementWraps() public pure {
        uint x = 2**256 - 1;
        unchecked {
            ++x;
        }
        assert(x == 0);
    }

    // open: design-limitation: unbounded integers, uint8 0 - 1 does not wrap to 255
    /// solc: smtCheckerTests/overflow/underflow_sub.sol
    function uncheckedUint8SubWraps() public pure {
        uint8 x = 0;
        uint8 y;
        unchecked {
            y = x - 1;
        }
        assert(y == 255);
        unchecked {
            y = x - 255;
        }
        assert(y == 1);
    }

    // open: design-limitation: unbounded integers, int8 127 + 1 does not wrap to -128
    /// solc: smtCheckerTests/overflow/overflow_sum_signed.sol
    function uncheckedInt8SumWraps() public pure {
        int8 x = 127;
        int8 y;
        unchecked {
            y = x + 1;
        }
        int8 e1 = -128;
        assert(y == e1);
        unchecked {
            y = x + 127;
        }
        int8 e2 = -2;
        assert(y == e2);
        x = -127;
        unchecked {
            y = x + -127;
        }
        assert(y == 2);
    }

    // open: design-limitation: unbounded integers, int8 100 * 2 does not wrap to -56
    /// solc: smtCheckerTests/overflow/overflow_mul_signed.sol
    function uncheckedInt8MulWraps() public pure {
        int8 x = 100;
        int8 y;
        unchecked {
            y = x * 2;
        }
        int8 e = -56;
        assert(y == e);
    }





}
