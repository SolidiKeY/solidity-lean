// SPDX-License-Identifier: GPL-3.0
pragma solidity 0.8.38;

type I8 is int8;
type I64 is int64;
type I256 is int256;
type U8 is uint8;
type B2 is bytes2;
using {complement8 as ~} for I8 global;
using {complement64 as ~} for I64 global;
using {complement256 as ~} for I256 global;
function complement8(I8 x) pure returns (I8) { return I8.wrap(~I8.unwrap(x)); }
function complement64(I64 x) pure returns (I64) { return I64.wrap(~I64.unwrap(x)); }
function complement256(I256 x) pure returns (I256) { return I256.wrap(~I256.unwrap(x)); }

contract OperatorBoundaries {
    I8 constant ZERO = I8.wrap(0);
    I8 constant MIN8 = I8.wrap(-128);
    I64 constant MIN64 = I64.wrap(type(int64).min);
    I256 constant MIN256 = I256.wrap(type(int256).min);
    U8 constant HIGH = U8.wrap(255);
    B2 constant PAD = B2.wrap(hex"1234");

    function boundaries() external pure {
        assert(I8.unwrap(~ZERO) == -1);
        assert(I8.unwrap(~MIN8) == 127);
        assert(I8.unwrap(~I8.wrap(127)) == -128);
        assert(I8.unwrap(~I8.wrap(-1)) == 0);
        assert(I64.unwrap(~MIN64) == type(int64).max);
        assert(I64.unwrap(~I64.wrap(type(int64).max)) == type(int64).min);
        assert(I256.unwrap(~MIN256) == type(int256).max);
        assert(I256.unwrap(~I256.wrap(type(int256).max)) == type(int256).min);
        assert(U8.unwrap(HIGH) == 255);
        assert(bytes4(B2.unwrap(PAD)) == hex"12340000");
    }
    function effects() external pure {
        int8 x = 1;
        assert(~x++ == -2);
        assert(x == 2);
        assert(I8.unwrap(~I8.wrap(x++)) == -3);
        assert(x == 3);
    }
    function uncheckedBoundaries() external pure {
        int8 x = -128;
        unchecked {
            assert(~x == 127);
            assert(I8.unwrap(~I8.wrap(x)) == 127);
        }
    }
    function falseComplement() external pure { assert(I8.unwrap(~ZERO) == 0); }
    function overloaded(int8 x) internal pure returns (int8) { return x + 42; }
    function controls() external pure { assert(overloaded(int8(1)) == 43); }
    function overloaded(I8 x) external pure returns (int8) { return I8.unwrap(x) + 1; }
    function overloaded(I64 x) external pure returns (int64) { return I64.unwrap(x) + 2; }
}
