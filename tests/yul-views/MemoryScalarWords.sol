// SPDX-License-Identifier: MIT
pragma solidity 0.8.38;
contract MemoryScalarWords {
    enum Choice { Zero, One, Two }
    struct S { int8 s8; int24 s24; uint8 u8; uint24 u24; address a; bytes3 b3; bytes31 b31; Choice e; MemoryScalarWords c; }
    function bounds() external pure returns (uint[16] memory) { return words(0); }
    function negativeOne() external pure returns (uint[16] memory) { return words(1); }
    function zero() external pure returns (uint[16] memory) { return words(2); }
    function maxima() external pure returns (uint[16] memory) { return words(3); }
    function revertWords() external pure { words(0); revert(); }
    function words(uint mode) internal pure returns (uint[16] memory out) {
        S memory s;
        s.s8 = mode == 0 ? type(int8).min : mode == 1 ? int8(-1) : mode == 2 ? int8(0) : type(int8).max;
        s.s24 = mode == 0 ? type(int24).min : mode == 1 ? int24(-1) : mode == 2 ? int24(0) : type(int24).max;
        s.u8 = mode == 0 ? type(uint8).max : mode == 1 ? uint8(1) : uint8(0);
        s.u24 = mode == 0 ? type(uint24).max : mode == 1 ? uint24(65535) : uint24(0);
        s.a = address(uint160(0x00112233445566778899aabbccddeeff0011223344));
        s.b3 = hex"112233";
        s.b31 = hex"0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f";
        s.e = mode == 0 ? Choice.Two : Choice.Zero;
        s.c = MemoryScalarWords(address(uint160(0x002233445566778899aabbccddeeff001122334455)));
        assembly ("memory-safe") {
            for { let i := 0 } lt(i, 9) { i := add(i, 1) } { mstore(add(out, mul(i, 32)), mload(add(s, mul(i, 32)))) }
        }
        out[9] = uint256(int256(s.s8)); out[10] = uint256(int256(s.s24));
        out[11] = s.u8; out[12] = s.u24; out[13] = uint(s.e);
        out[14] = uint8(s.b3[0]); out[15] = uint8(s.b31[30]);
    }
}
