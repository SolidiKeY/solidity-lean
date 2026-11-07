// SPDX-License-Identifier: MIT
pragma solidity 0.8.38;

// Explicit ordinary owned pool, exact header/element/alias observations. No
// source/compiler correspondence or universal allocator assertion is implied.
contract DynamicUint {
    function initial() external pure returns (bytes memory) { run(0); }
    function changed() external pure returns (bytes memory) { run(1); }
    function shrinkZero() external pure returns (bytes memory) { run(2); }
    function regrowOne() external pure returns (bytes memory) { run(3); }
    function regrowAll() external pure returns (bytes memory) { run(4); }
    function firstThenSecond() external pure returns (bytes memory) { run(5); }
    function secondThenFirst() external pure returns (bytes memory) { run(6); }
    function revertChanges() external pure { run(7); }
    function run(uint mode) internal pure {
        uint start;
        assembly ("memory-safe") { start := mload(0x40) mstore(0x40, add(start, 1024)) }
        uint[] memory a;
        uint[] memory b;
        bytes memory other;
        uint[][] memory aliases;
        assembly ("memory-safe") {
            a := start b := add(start, 256) other := add(start, 512) aliases := add(start, 768)
            for { let p := start } lt(p, add(start, 1024)) { p := add(p, 32) } {
                mstore(p, 0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5)
            }
            mstore(a, 3) mstore(add(a, 32), 7) mstore(add(a, 64), 9) mstore(add(a, 96), not(0))
            mstore(b, 2) mstore(add(b, 32), 11) mstore(add(b, 64), 13)
            mstore(other, 3) mstore(add(other, 32), 0xeeddcca5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5)
            mstore(aliases, 2) mstore(add(aliases, 32), a) mstore(add(aliases, 64), a)
        }
        if (mode == 1) { a[0] = type(uint256).max; a[1] = 42; a[2] = 0; }
        if (mode >= 2 && mode <= 4) {
            assembly ("memory-safe") { mstore(a, 0) }
            if (mode == 3) { assembly ("memory-safe") { mstore(a, 1) } }
            if (mode == 4) { assembly ("memory-safe") { mstore(a, 3) } }
        }
        if (mode == 5) { a[0] = type(uint256).max; a[1] = 42; a[2] = 0; b[0] = type(uint256).max; b[1] = 0; }
        if (mode == 6) { b[0] = type(uint256).max; b[1] = 0; a[0] = type(uint256).max; a[1] = 42; a[2] = 0; }
        if (mode == 7) { a[0] = 42; b[0] = 43; revert(); }
        uint oldFree;
        assembly ("memory-safe") { oldFree := mload(0x40) }
        uint[32] memory out;
        assembly ("memory-safe") {
            mstore(out, mload(a)) mstore(add(out, 32), mload(add(a, 32)))
            mstore(add(out, 64), mload(add(a, 64))) mstore(add(out, 96), mload(add(a, 96)))
            mstore(add(out, 128), mload(b)) mstore(add(out, 160), mload(add(b, 32))) mstore(add(out, 192), mload(add(b, 64)))
            mstore(add(out, 224), mload(other)) mstore(add(out, 256), mload(add(other, 32)))
            mstore(add(out, 288), mload(aliases)) mstore(add(out, 320), mload(add(aliases, 32))) mstore(add(out, 352), mload(add(aliases, 64)))
            mstore(add(out, 416), mload(0x60))
            mstore(add(out, 768), mload(add(a, 128))) mstore(add(out, 800), mload(add(b, 96)))
            mstore(add(out, 832), mload(add(other, 64))) mstore(add(out, 864), mload(add(aliases, 96)))
            mstore(add(out, 896), a) mstore(add(out, 928), b) mstore(add(out, 960), other) mstore(add(out, 992), aliases)
        }
        out[12] = oldFree;
        out[14] = a.length; out[15] = aliases[0].length; out[16] = aliases[1].length;
        out[17] = a.length > 0 ? a[0] : 0;
        out[18] = a.length > 1 ? aliases[0][1] : 0;
        out[19] = a.length > 2 ? aliases[1][2] : 0;
        out[20] = b[0]; out[21] = b[1]; out[22] = uint8(other[0]); out[23] = uint8(other[2]);
        assembly ("memory-safe") {
            let result := mload(0x40)
            mstore(result, 32) mstore(add(result, 32), 1024)
            mcopy(add(result, 64), out, 1024)
            return(result, 1088)
        }
    }
}
