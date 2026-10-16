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

    // open: true-fact-unprovable: smod(42, y) has no sign lemma, goal leq(smod(42, y), -1) ==> y = 0
    /// solc: smtCheckerTests/operators/mod_signed.sol
    /// @custom:key box
    function modSignFollowsDividend(int x, int y) public pure {
        require(y != 0 && x == 42);
        int z1 = x % y;
        assert((x >= 0 && z1 >= 0) || (x <= 0 && z1 <= 0));
    }

    // open: true-fact-unprovable: smod(x, y) < y is not derived, goal geq(smod(x, y), y), geq(y, 1) ==>
    /// solc: smtCheckerTests/operators/mod_n.sol
    /// @custom:key box
    function modBelowDivisor(uint x, uint y) public pure {
        require(y > 0);
        uint z = x % y;
        assert(z < y);
    }

    // open: true-fact-unprovable: goal leq(x, 9999) ==> smod(mul(x, 2), 2) = 0
    /// solc: smtCheckerTests/operators/mod_even.sol
    /// @custom:key box
    function modOfDoubleIsZero(uint x) public pure {
        require(x < 10000);
        uint y = x * 2;
        uint m = y % 2;
        assert(m == 0);
    }

    // open: true-fact-unprovable: a uint parameter carries no 0 <= x fact, goal leq(x, -1) ==>
    /// solc: smtCheckerTests/operators/compound_sub.sol
    /// @custom:key box
    function compoundSubSelfReference(uint x) public pure {
        require(x < 100);
        uint y = 200;
        y -= y - x;
        assert(y >= 0);
    }

    // open: true-fact-unprovable: a uint parameter carries no 0 <= x fact, goal leq(x, -1) ==>
    /// solc: smtCheckerTests/operators/compound_sub_mapping.sol
    /// @custom:key box
    function compoundSubMapping(uint x, uint p) public {
        require(x < 100);
        map[p] = 200;
        map[p] -= map[p] - x;
        uint r = map[p];
        assert(r >= 0);
    }

    // open: true-fact-unprovable: a uint parameter carries no 0 <= x fact, goal leq(x, -1) ==>
    /// solc: smtCheckerTests/operators/compound_sub_array_index.sol
    /// @custom:key box
    function compoundSubArrayIndex(uint x, uint p) public {
        require(p < array.length);
        require(x < 100);
        array[p] = 200;
        array[p] -= array[p] - x;
        uint r = array[p];
        assert(r >= 0);
    }

    // open: unsupported-construct: a compound assignment used as a value (u = (b += c);) has no rule
    /// solc: smtCheckerTests/operators/compound_add_chain.sol
    function compoundAddChain() public pure {
        uint a = 1;
        uint b = 3;
        uint c = 7;
        a += b += c;
        assert(b == 10 && a == 11);
        a += (b += c);
        assert(b == 17 && a == 28);
        a += a += a;
        assert(a == 112);
    }

    // open: unsupported-construct: an expression statement (a + b;) in the modifier has no rule
    /// solc: semanticTests/arithmetics/checked_modifier_called_by_unchecked.sol
    /// @custom:key box
    function checkedModifierCalledByUnchecked(uint a, uint b, uint c) public pure addUnchecked(a, b) {
        require(a == 0xe000 && b == 0xe500 && c == 2);
        uint r = b + c;
        assert(r == 58626);
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

    // open: unsupported-construct: << has no rule, stuck on r = a_0 << b_0;
    /// solc: semanticTests/operators/shifts/shift_left.sol
    /// @custom:key box
    function shiftLeftParam(uint a, uint b) public pure {
        require(a == 0x4266 && b == 8);
        uint r = a << b;
        assert(r == 0x426600);
    }

    // open: unsupported-construct: >> has no rule, stuck on r = a_0 >> b_0;
    /// solc: semanticTests/operators/shifts/shift_right.sol
    /// @custom:key box
    function shiftRightParam(uint a, uint b) public pure {
        require(a == 0x4266 && b == 8);
        uint r = a >> b;
        assert(r == 0x42);
    }

    // open: unsupported-construct: >>= has no rule, stuck on a >>= 8;
    /// solc: semanticTests/operators/shifts/shift_constant_right_assignment.sol
    function shiftRightAssign() public pure {
        uint a = 0x4200;
        a >>= 8;
        assert(a == 0x42);
    }

    // open: unsupported-construct: >> has no rule, stuck on r = -4266 >> 1;
    /// solc: semanticTests/operators/shifts/shift_right_negative_literal.sol
    function shiftRightNegativeLiteral() public pure {
        int r = -4266 >> 1;
        int e = -2133;
        assert(r == e);
    }
}
