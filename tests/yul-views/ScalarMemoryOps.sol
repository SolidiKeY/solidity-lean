// SPDX-License-Identifier: MIT
pragma solidity 0.8.38;
contract ScalarMemoryOps {
    struct S { int8 signedValue; address addr; bytes3 data; }
    function initial() external pure returns (bytes memory) { run(0); }
    function changed() external pure returns (bytes memory) { run(1); }
    function reversed() external pure returns (bytes memory) { run(2); }
    function shrinkZero() external pure returns (bytes memory) { run(3); }
    function regrow() external pure returns (bytes memory) { run(4); }
    function partialRegrow() external pure returns (bytes memory) { run(5); }
    function revertOps() external pure { run(6); }
    function run(uint mode) internal pure {
        uint start;
        assembly ("memory-safe") { start := mload(0x40) mstore(0x40, add(start, 1280)) }
        S memory s; int8[4] memory a; bytes3[] memory b; address[] memory c; bytes memory other;
        assembly ("memory-safe") {
            s := start a := add(start, 256) b := add(start, 512) c := add(start, 768) other := add(start, 1024)
            for { let p := start } lt(p, add(start, 1280)) { p := add(p, 32) } {
                mstore(p, 0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5)
            }
            mstore(s, sub(0, 128)) mstore(add(s, 32), 0x1234) mstore(add(s, 64), shl(232, 0x112233))
            mstore(a, sub(0, 128)) mstore(add(a, 32), not(0)) mstore(add(a, 64), 0) mstore(add(a, 96), 127)
            mstore(b, 2) mstore(add(b, 32), shl(232, 0x112233)) mstore(add(b, 64), shl(232, 0xaa00ff))
            mstore(c, 2) mstore(add(c, 32), 0x1234) mstore(add(c, 64), sub(shl(160, 1), 1))
            mstore(other, 3) mstore(add(other, 32), shl(232, 0xeeddcc))
        }
        if (mode == 2) {
            c[1] = address(0); c[0] = address(type(uint160).max); b[1] = hex"010203"; b[0] = hex"ff00aa";
            a[3] = 0; a[2] = -128; a[1] = 127; a[0] = -1;
            s.data = hex"ff00aa"; s.addr = address(type(uint160).max); s.signedValue = -1;
        } else if (mode == 1 || mode == 6) {
            s.signedValue = -1; s.addr = address(type(uint160).max); s.data = hex"ff00aa";
            a[0] = -1; a[1] = 127; a[2] = -128; a[3] = 0;
            b[0] = hex"ff00aa"; b[1] = hex"010203"; c[0] = address(type(uint160).max); c[1] = address(0);
        }
        if (mode >= 3 && mode <= 5) {
            assembly ("memory-safe") { mstore(b, 0) mstore(c, 0) }
            if (mode >= 4) { assembly ("memory-safe") { mstore(b, 2) mstore(c, 2) } }
            if (mode == 5) { assembly ("memory-safe") { mstore(b, 1) mstore(c, 1) } }
        }
        if (mode == 6) revert();
        uint oldFree;
        assembly ("memory-safe") { oldFree := mload(0x40) }
        uint[36] memory out;
        assembly ("memory-safe") {
            mstore(add(out, 0), mload(s))
            mstore(add(out, 32), mload(add(s, 32)))
            mstore(add(out, 64), mload(add(s, 64)))
            mstore(add(out, 96), mload(add(a, 0)))
            mstore(add(out, 128), mload(add(a, 32)))
            mstore(add(out, 160), mload(add(a, 64)))
            mstore(add(out, 192), mload(add(a, 96)))
            mstore(add(out, 224), mload(b))
            mstore(add(out, 256), mload(add(b, 32)))
            mstore(add(out, 288), mload(add(b, 64)))
            mstore(add(out, 320), mload(c))
            mstore(add(out, 352), mload(add(c, 32)))
            mstore(add(out, 384), mload(add(c, 64)))
            mstore(add(out, 416), mload(other))
            mstore(add(out, 448), mload(add(other, 32)))
            mstore(add(out, 512), mload(0x60))
            mstore(add(out, 544), mload(add(s, 96)))
            mstore(add(out, 576), mload(add(a, 128)))
            mstore(add(out, 608), mload(add(b, 96)))
            mstore(add(out, 640), mload(add(c, 96)))
            mstore(add(out, 672), mload(add(other, 64)))
            mstore(add(out, 1120), mload(add(b, 64)))
        }
        out[15] = oldFree;
        out[22] = uint256(int256(s.signedValue)); out[23] = uint160(s.addr); out[24] = uint8(s.data[0]);
        out[25] = uint256(int256(a[0])); out[26] = uint256(int256(a[3])); out[27] = b.length;
        out[28] = b.length > 0 ? uint8(b[0][0]) : 0;
        out[29] = c.length; out[30] = c.length > 0 ? uint160(c[0]) : 0;
        out[31] = uint8(other[0]); out[32] = uint8(other[2]);
        out[33] = b.length; out[34] = b.length > 0 ? uint8(b[0][0]) : 0;
        assembly ("memory-safe") {
            let result := mload(0x40)
            mstore(result, 32) mstore(add(result, 32), 1152)
            mcopy(add(result, 64), out, 1152)
            return(result, 1216)
        }
    }
}
