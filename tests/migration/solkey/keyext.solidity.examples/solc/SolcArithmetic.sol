// SPDX-License-Identifier: GPL-2.0-only
pragma solidity ^0.8.0;

/// Ports of semanticTests/{arithmetics,exponentiation,integer,operators} and
/// smtCheckerTests/{operators,overflow}.
contract SolcArithmetic {
    uint value1;
    uint value2;
    mapping(uint => uint) map;
    uint[] array;
    uint[] pushed;
    uint constant DEPTH = 32;
    uint constant MAX_COUNT = 2**DEPTH - 1;
    uint constant CX = 7;
    uint constant CY = 3;
    uint constant CZ = CX / CY;
    uint constant EX = 2;
    uint constant EY = EX ** 10;
    int256 constant SIGNED_CONSTANT = 42;

    /// solc: semanticTests/arithmetics/divisiod_by_zero.sol
    /// @custom:key box
    function divisionTruncates(uint a, uint b) public pure {
        require(a == 7 && b == 2);
        uint r = a / b;
        assert(r == 3);
    }

    /// solc: semanticTests/arithmetics/divisiod_by_zero.sol
    /// @custom:key box
    function moduloRemainder(uint a, uint b) public pure {
        require(a == 7 && b == 2);
        uint r = a % b;
        assert(r == 1);
    }

    /// solc: semanticTests/arithmetics/unchecked_div_by_zero.sol
    /// @custom:key box
    function uncheckedDivision(uint a, uint b) public pure {
        require(a == 7 && b == 2);
        uint r;
        unchecked {
            r = a / b;
        }
        assert(r == 3);
    }

    /// solc: semanticTests/arithmetics/unchecked_div_by_zero.sol
    /// @custom:key box
    function uncheckedModulo(uint a, uint b) public pure {
        require(a == 7 && b == 2);
        uint r;
        unchecked {
            r = a % b;
        }
        assert(r == 1);
    }

    /// solc: semanticTests/arithmetics/signed_mod.sol
    /// @custom:key box
    function signedModPositive(int a, int b) public pure {
        require(a == 7 && b == 5);
        int r = a % b;
        assert(r == 2);
    }

    /// solc: semanticTests/arithmetics/signed_mod.sol
    /// @custom:key box
    function signedModNegativeDivisor(int a, int b) public pure {
        int minusFive = -5;
        require(a == 7 && b == minusFive);
        int r = a % b;
        assert(r == 2);
    }

    /// solc: semanticTests/arithmetics/signed_mod.sol
    /// @custom:key box
    function signedModNegativeDividend(int a, int b) public pure {
        int minusSeven = -7;
        require(a == minusSeven && b == 5);
        int r = a % b;
        int expected = -2;
        assert(r == expected);
    }

    /// solc: semanticTests/arithmetics/signed_mod.sol
    /// @custom:key box
    function signedModBothNegative(int a, int b) public pure {
        int minusFive = -5;
        require(a == minusFive && b == minusFive);
        int r = a % b;
        assert(r == 0);
    }

    /// solc: semanticTests/arithmetics/exp_associativity.sol
    /// @custom:key box
    function expRightAssociativeThree(uint a, uint b, uint c) public pure {
        require(a == 2 && b == 3 && c == 4);
        uint r = a ** b ** c;
        assert(r == 2417851639229258349412352);
    }

    /// solc: semanticTests/arithmetics/exp_associativity.sol
    /// @custom:key box
    function expRightAssociativeFour(uint a, uint b, uint c, uint d) public pure {
        require(a == 3 && b == 2 && c == 2 && d == 2);
        uint r = a ** b ** c ** d;
        assert(r == 43046721);
    }

    /// solc: semanticTests/arithmetics/exp_associativity.sol
    /// @custom:key box
    function expInvariant(uint a, uint b, uint c) public pure {
        require(a == 3 && b == 4 && c == 2);
        uint l = a ** b ** c;
        uint r = a ** (b ** c);
        assert(l == r);
    }

    /// solc: semanticTests/arithmetics/exp_associativity.sol
    /// @custom:key box
    function expLiteralMix(uint a, uint b) public pure {
        require(a == 2 && b == 3);
        uint l1 = a ** 2 ** b;
        uint r1 = a ** (2 ** b);
        uint l2 = 2 ** a ** b;
        uint r2 = 2 ** (a ** b);
        uint l3 = a ** b ** 2;
        uint r3 = a ** (b ** 2);
        assert(l1 == r1);
        assert(l2 == r2);
        assert(l3 == r3);
    }

    /// solc: semanticTests/arithmetics/exp_associativity.sol
    /// @custom:key box
    function expOtherOperators(uint a, uint b) public pure {
        require(a == 2 && b == 4);
        uint l1 = a ** b / 25;
        uint r1 = (a ** b) / 25;
        uint l2 = a ** b * 3 ** b;
        uint r2 = (a ** b) * (3 ** b);
        uint l3 = b ** a ** a / b ** a ** b;
        uint r3 = (b ** (a ** a)) / (b ** (a ** b));
        assert(l1 == r1);
        assert(l2 == r2);
        assert(l3 == r3);
    }

    /// solc: semanticTests/exponentiation/literal_base.sol
    /// @custom:key box
    function literalBaseThirteen(uint x) public pure {
        require(x == 13);
        uint a;
        int b;
        unchecked {
            a = 2 ** x;
            b = -2 ** x;
        }
        int expected = -8192;
        assert(a == 8192);
        assert(b == expected);
    }

    /// solc: semanticTests/exponentiation/literal_base.sol
    /// @custom:key box
    function literalBaseEvenExponent(uint x) public pure {
        require(x == 2);
        uint a;
        int b;
        unchecked {
            a = 2 ** x;
            b = -2 ** x;
        }
        assert(a == 4);
        assert(b == 4);
    }

    /// solc: semanticTests/integer/small_signed_types.sol
    function smallSignedTypesProduct() public pure {
        int r = -int32(10) * -int64(20);
        assert(r == 200);
    }

    /// solc: semanticTests/integer/many_local_variables.sol
    /// @custom:key box
    function manyLocalVariables(uint x1, uint x2, uint x3) public pure {
        require(x1 == 4096 && x2 == 65536 && x3 == 1048576);
        uint8 a = 0x1;
        uint8 b = 0x10;
        uint16 c = 0x100;
        uint y = a + b + c + x1 + x2 + x3;
        y += b + x2;
        assert(y == 0x121121);
    }

    function compoundAssignStep(uint x, uint y) internal returns (uint) {
        uint value3 = y;
        value1 += x;
        value3 *= x;
        uint v1 = value1;
        value2 *= value3 + v1;
        value2 += 7;
        uint w = value2;
        return w;
    }

    /// solc: semanticTests/operators/compound_assign.sol
    /// @custom:key box
    function compoundAssignSequence() public {
        require(value1 == 0 && value2 == 0);
        uint w1 = compoundAssignStep(0, 6);
        assert(w1 == 7);
        uint w2 = compoundAssignStep(1, 3);
        assert(w2 == 0x23);
        uint w3 = compoundAssignStep(2, 25);
        assert(w3 == 0x0746);
    }

    /// solc: smtCheckerTests/operators/division_truncates_correctly_1.sol
    /// @custom:key box
    function divisionTruncatesUnsigned(uint x, uint y) public pure {
        require(x == 0 && y == 0);
        x = 7;
        y = 2;
        uint r = x / y;
        assert(r == 3);
    }

    /// solc: smtCheckerTests/operators/division_truncates_correctly_2.sol
    /// @custom:key box
    function divisionTruncatesSignedPositive(int x, int y) public pure {
        require(x == 0 && y == 0);
        x = 7;
        y = 2;
        int r = x / y;
        assert(r == 3);
    }

    /// solc: smtCheckerTests/operators/division_truncates_correctly_3.sol
    /// @custom:key box
    function divisionTruncatesNegativeDividend(int x, int y) public pure {
        require(x == 0 && y == 0);
        x = -7;
        y = 2;
        int r = x / y;
        int expected = -3;
        assert(r == expected);
    }

    /// solc: smtCheckerTests/operators/division_truncates_correctly_4.sol
    /// @custom:key box
    function divisionTruncatesNegativeDivisor(int x, int y) public pure {
        require(x == 0 && y == 0);
        x = 7;
        y = -2;
        int r = x / y;
        int expected = -3;
        assert(r == expected);
    }

    /// solc: smtCheckerTests/operators/division_truncates_correctly_5.sol
    /// @custom:key box
    function divisionTruncatesBothNegative(int x, int y) public pure {
        require(x == 0 && y == 0);
        x = -7;
        y = -2;
        int r = x / y;
        assert(r == 3);
    }

    /// solc: smtCheckerTests/operators/mod.sol
    /// @custom:key box
    function modSignIgnoresDivisor(int x, int y) public pure {
        int minusTen = -10;
        require(y == minusTen && x == 100);
        int z1 = x % y;
        int z2 = x % -y;
        assert(z1 == z2);
    }

    /// solc: smtCheckerTests/operators/compound_add.sol
    /// @custom:key box
    function compoundAddSelfReference(uint x) public pure {
        require(x < 100);
        uint y = 100;
        y += y + x;
        assert(y < 300);
    }

    /// solc: smtCheckerTests/operators/compound_mul.sol
    /// @custom:key box
    function compoundMulSelfReference(uint x) public pure {
        require(x < 10);
        uint y = 10;
        y *= y + x;
        assert(y <= 190);
    }

    /// solc: smtCheckerTests/operators/compound_assignment_division_1.sol
    /// @custom:key box
    function compoundDivSelfReference(uint x) public pure {
        require(x == 2);
        uint y = 10;
        y /= y / x;
        assert(y == x);
    }

    /// solc: smtCheckerTests/operators/compound_add_mapping.sol
    /// @custom:key box
    function compoundAddMapping(uint x, uint p) public {
        require(x < 100);
        map[p] = 100;
        map[p] += map[p] + x;
        uint r = map[p];
        assert(r < 300);
    }

    /// solc: smtCheckerTests/operators/compound_mul_mapping.sol
    /// @custom:key box
    function compoundMulMapping(uint x, uint p) public {
        require(x < 10);
        map[p] = 10;
        map[p] *= map[p] + x;
        uint r = map[p];
        assert(r <= 190);
    }

    /// solc: smtCheckerTests/operators/compound_assignment_division_3.sol
    /// @custom:key box
    function compoundDivMapping(uint x, uint p) public {
        require(x == 2);
        map[p] = 10;
        map[p] /= map[p] / x;
        uint r = map[p];
        assert(r == x);
    }

    /// solc: smtCheckerTests/operators/compound_add_array_index.sol
    /// @custom:key box
    function compoundAddArrayIndex(uint x, uint p) public {
        require(p < array.length);
        require(x < 100);
        array[p] = 100;
        array[p] += array[p] + x;
        uint r = array[p];
        assert(r < 300);
    }

    /// solc: smtCheckerTests/operators/compound_mul_array_index.sol
    /// @custom:key box
    function compoundMulArrayIndex(uint x, uint p) public {
        require(p < array.length);
        require(x < 10);
        array[p] = 10;
        array[p] *= array[p] + x;
        uint r = array[p];
        assert(r <= 190);
    }

    /// solc: smtCheckerTests/operators/compound_assignment_division_2.sol
    /// @custom:key box
    function compoundDivArrayIndex(uint x, uint p) public {
        require(p < array.length);
        require(x == 2);
        array[p] = 10;
        array[p] /= array[p] / x;
        uint r = array[p];
        assert(r == x);
    }

    /// solc: smtCheckerTests/operators/unary_add.sol
    function unaryAddLocal() public pure {
        uint x = 2;
        uint a = ++x;
        assert(x == 3);
        assert(a == 3);
        uint b = x++;
        assert(x == 4);
        assert(b == 3);
    }

    /// solc: smtCheckerTests/operators/unary_sub.sol
    function unarySubLocal() public pure {
        uint x = 5;
        uint a = --x;
        assert(x == 4);
        assert(a == 4);
        uint b = x--;
        assert(x == 3);
        assert(b == 4);
    }

    /// solc: smtCheckerTests/operators/unary_add_mapping.sol
    /// @custom:key box
    function unaryAddMapping(uint x) public {
        require(x == 1);
        map[x] = 2;
        uint a = ++map[x];
        uint m1 = map[x];
        assert(m1 == 3);
        assert(a == 3);
        uint b = map[x]++;
        uint m2 = map[x];
        assert(m2 == 4);
        assert(b == 3);
    }

    /// solc: smtCheckerTests/operators/unary_sub_mapping.sol
    /// @custom:key box
    function unarySubMapping(uint x) public {
        require(x == 1);
        map[x] = 5;
        uint a = --map[x];
        uint m1 = map[x];
        assert(m1 == 4);
        assert(a == 4);
        uint b = map[x]--;
        uint m2 = map[x];
        assert(m2 == 3);
        assert(b == 4);
    }

    /// solc: smtCheckerTests/operators/unary_add_array.sol
    /// @custom:key box
    function unaryAddArray(uint x) public {
        require(x < array.length);
        array[x] = 2;
        uint a = ++array[x];
        uint m1 = array[x];
        assert(m1 == 3);
        assert(a == 3);
        uint b = array[x]++;
        uint m2 = array[x];
        assert(m2 == 4);
        assert(b == 3);
    }

    /// solc: smtCheckerTests/operators/unary_sub_array.sol
    /// @custom:key box
    function unarySubArray(uint x) public {
        require(x < array.length);
        array[x] = 5;
        uint a = --array[x];
        uint m1 = array[x];
        assert(m1 == 4);
        assert(a == 4);
        uint b = array[x]--;
        uint m2 = array[x];
        assert(m2 == 3);
        assert(b == 4);
    }

    /// solc: smtCheckerTests/overflow/overflow_and_underflow_chc.sol
    /// @custom:key box
    function signedSumOfZeros(int x, int y) public pure {
        require(x == 0 && y == 0);
        int r = x + y;
        assert(r == 0);
    }

    /// solc: smtCheckerTests/overflow/unsigned_guard_sub_overflow.sol
    /// @custom:key box
    function guardedSubtractionNonNegative(uint x, uint y) public pure {
        require(x >= y);
        uint r = x - y;
        assert(r >= 0);
    }

    function addUnchecked16(uint16 a, uint16 b) internal pure returns (uint16) {
        unchecked {
            return a + b;
        }
    }

    /// solc: semanticTests/arithmetics/unchecked_called_by_checked.sol
    /// @custom:key box
    function uncheckedCalledByChecked(uint16 a) public pure {
        require(a == 7);
        uint16 r = addUnchecked16(a, 0x100) + 0x100;
        assert(r == 0x0207);
    }

    /// solc: smtCheckerTests/operators/constant_propagation_1.sol
    function constantPropagationPower() public pure {
        uint d = DEPTH;
        uint m = MAX_COUNT;
        assert(d == 32);
        assert(m == 4294967295);
    }

    /// solc: smtCheckerTests/operators/constant_propagation_2.sol
    function constantPropagationDivision() public pure {
        uint z = CZ;
        uint a = CX / 3;
        uint b = 7 / CY;
        uint c = CZ * 3;
        assert(z == 2);
        assert(z == a);
        assert(z == b);
        assert(c != 7);
    }

    /// solc: smtCheckerTests/operators/const_exp_1.sol
    function constantExponent() public pure {
        uint y = EY;
        uint e = 2 ** 10;
        assert(y == e);
        assert(y == 1024);
    }

    /// solc: smtCheckerTests/operators/constant_evaluation_unary_minus_chc.sol
    function constantUnaryMinus() public pure {
        int r = -SIGNED_CONSTANT;
        int expected = -42;
        assert(r == expected);
    }

    /// solc: smtCheckerTests/operators/unary_add_array_push_1.sol
    /// @custom:key box
    function unaryAddOnPush() public {
        require(pushed.length == 0);
        ++pushed.push();
        uint len = pushed.length;
        uint r = pushed[0];
        assert(len == 1);
        assert(r == 1);
    }
}
