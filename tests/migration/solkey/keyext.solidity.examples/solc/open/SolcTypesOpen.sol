// SPDX-License-Identifier: GPL-2.0-only
pragma solidity ^0.8.0;

/// Ports of semanticTests/{enums,literals,types} and smtCheckerTests/{types,typecast} that load
/// but do not close (or close but fail on the EVM).
contract SolcTypesOpen {
    enum Truth { False, True }
    enum ActionChoices { GoLeft, GoRight, GoStraight }
    enum D { Left, Right }

    ActionChoices choice;
    address a;
    uint c;

    /// solc: semanticTests/enums/constructing_enums_from_ints.sol
    function constructingEnumsFromInts() public pure {
        // open: no rule executes an integer-to-enum conversion E(x); the proof stops on it
        uint r = uint256(Truth(uint8(0x1)));
        assert(r == 1);
    }

    /// solc: semanticTests/enums/enum_explicit_overflow.sol
    function enumExplicitConversionInRange() public {
        // open: no rule executes an integer-to-enum conversion E(x); the proof stops on it
        uint x = 2;
        choice = ActionChoices(x);
        uint r = uint256(choice);
        assert(r == 2);
    }

    /// solc: smtCheckerTests/typecast/enum_from_uint.sol
    /// @custom:key box
    function enumFromUint(uint x) public pure {
        // open: no rule executes an integer-to-enum conversion E(x); the proof stops on it
        require(x == 0);
        D p = D(x);
        assert(p == D.Left);
    }

    /// solc: smtCheckerTests/types/enum_range.sol
    function enumRange(D p) public pure {
        // open: an enum parameter is an unconstrained int, its member range is not assumed
        assert(p == D.Left || p == D.Right);
    }

    /// solc: smtCheckerTests/typecast/enum_to_uint_max_value.sol
    function enumToUintMaxValue(D p) public pure {
        // open: an enum parameter is an unconstrained int, its member range is not assumed
        uint x = uint(p);
        assert(x < 10);
    }

    /// solc: smtCheckerTests/types/storage_value_vars_3.sol
    /// @custom:key box
    function storageValueVarsNonNegative() public view {
        // open: a uint state variable read from storage is not known to be non-negative
        require(a < 0x0000000000000000000000000000000000000100);
        assert(c >= 0);
    }

    /// solc: smtCheckerTests/typecast/cast_larger_1.sol
    function castLargerKeepsRange(uint8 x) public pure {
        // open: a uint8 parameter is an unbounded int, its 0..255 range is not assumed
        uint16 y = uint16(x);
        assert(y < 300);
    }

    /// solc: smtCheckerTests/typecast/cast_smaller_1.sol
    function castSmallerBoundsRange(uint16 x) public pure {
        // open: the narrowing cast uint8(x) is the identity, so y is not bounded by 255
        uint8 y = uint8(x);
        assert(y < 300);
    }

    /// solc: smtCheckerTests/typecast/cast_smaller_2.sol
    function castSmallerTruncates() public pure {
        // open: the narrowing cast uint16(a) is the identity instead of truncating
        uint32 p = 0x12345678;
        uint16 q = uint16(p);
        assert(q == 0x5678);
    }

    /// solc: smtCheckerTests/typecast/downcast.sol
    function downcastTruncates() public pure {
        // open: narrowing and sign-changing casts are the identity instead of wrapping
        int8 y = int8(uint8(uint16(200)));
        uint8 v = uint8(int8(int16(300)));
        int8 e = -56;
        assert(y == e);
        assert(v == 44);
    }

    /// solc: smtCheckerTests/typecast/same_size.sol
    function sameSizeReinterprets() public pure {
        // open: a same-width signed/unsigned cast is the identity instead of reinterpreting the bits
        int8 p = int8(uint8(200));
        uint8 q = uint8(int8(-100));
        int8 e = -56;
        assert(p == e);
        assert(q == 156);
    }

    /// solc: smtCheckerTests/typecast/upcast.sol
    function upcastAfterTruncation() public pure {
        // open: int8(int(255)) is the identity instead of wrapping to -1
        int z = int(int8(int(255)));
        int e = -1;
        assert(z == e);
    }

    /// solc: smtCheckerTests/typecast/number_literal.sol
    function numberLiteralWraps() public pure {
        // open: uint(int(-1)) is the identity instead of wrapping to 2**256-1
        uint b = 115792089237316195423570985008687907853269984665640564039457584007913129639935;
        int d = -1;
        uint e = uint(d);
        assert(b == e);
    }

    /// solc: semanticTests/types/type_conversion_cleanup.sol
    function typeConversionCleanup() public pure {
        // open: uint128(x) is the identity instead of truncating to the low 128 bits
        uint200 mx = 1606938044258990275541962092341162602522202993782792835301375;
        uint r = uint(uint160(address(uint160(uint128(mx)))));
        assert(r == 0xffffffffffffffffffffffffffffffff);
    }

    /// solc: semanticTests/types/packing_signed_types.sol
    function packingSignedTypes() public pure {
        // open: int8(uint8 0xfa) is the identity instead of reinterpreting to -6
        uint8 x = 0xfa;
        int8 y = int8(x);
        int8 e = -6;
        assert(y == e);
    }

    /// solc: semanticTests/types/nested_tuples.sol
    function nestedTuplesParenthesized() public pure {
        // open: a parenthesized tuple target ((a, b)) = (...) has no rule
        int x;
        bool b;
        ((x, b)) = (2, true);
        assert(x == 2);
        assert(b);
    }

    // open: closes in KeY, but the uint8 addition 63 + 255 panics with 0x11 on the EVM
    /// solc: semanticTests/literals/ternary_operator_with_literal_types_overflow.sol
    function ternaryLiteralOverflow() public pure {
        bool t = true;
        bool f = false;
        uint16 r = (t ? 63 : 255) + (f ? 63 : 255);
        assert(r == 318);
    }
}
