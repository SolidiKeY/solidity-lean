// SPDX-License-Identifier: MIT
pragma solidity 0.8.38;

// Ordinary allocated object/reference evidence, not frontend/correspondence support.
contract HeapBytes {
    function objects() internal pure returns (bytes memory a, string memory b, bytes memory c) {
        assembly ("memory-safe") {
            let start := mload(0x40)
            a := start
            b := add(start, 128)
            c := add(start, 256)
            mstore(0x40, add(start, 384))
            mstore(a, 3)
            mstore(add(a, 32), 0x112233a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5)
            mstore(add(a, 64), 0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5)
            mstore(add(a, 96), 0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5)
            mstore(b, 33)
            mstore(add(b, 32), 0x6161616161616161616161616161616161616161616161616161616161616161)
            mstore(add(b, 64), 0x61a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5)
            mstore(add(b, 96), 0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5)
            mstore(c, 3)
            mstore(add(c, 32), 0xeeddcca5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5)
            mstore(add(c, 64), 0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5)
            mstore(add(c, 96), 0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5)
        }
    }
    function changeA(bytes memory a) internal pure { a[0] = 0x99; a[1] = 0x88; a[2] = 0x77; }
    function changeB(string memory b) internal pure {
        bytes memory aliasB = bytes(b);
        for (uint i = 0; i < 33; ++i) aliasB[i] = i == 0 ? bytes1(0xff) : bytes1(0x62);
    }
    function observe(bytes memory a, string memory b, bytes memory c, bytes memory aliasA, string memory aliasS)
        internal pure returns (bytes memory) {
        uint8 viaBytes = uint8(aliasA[0]);
        uint8 viaString = uint8(bytes(aliasS)[0]);
        assembly ("memory-safe") {
            let out := mload(0x40)
            mstore(out, 32)
            mstore(add(out, 32), 512)
            let data := add(out, 64)
            mstore(data, mload(a))
            mstore(add(data, 32), mload(add(a, 32)))
            mstore(add(data, 64), mload(b))
            mstore(add(data, 96), mload(add(b, 32)))
            mstore(add(data, 128), mload(add(b, 64)))
            mstore(add(data, 160), mload(c))
            mstore(add(data, 192), mload(add(c, 32)))
            mstore(add(data, 224), mload(0x40))
            mstore(add(data, 256), mload(0x60))
            mstore(add(data, 288), mload(add(a, 64)))
            mstore(add(data, 320), mload(add(b, 96)))
            mstore(add(data, 352), mload(add(c, 64)))
            mstore(add(data, 384), viaBytes)
            mstore(add(data, 416), viaString)
            mstore(add(data, 448), eq(a, aliasA))
            mstore(add(data, 480), eq(a, aliasS))
            return(out, 576)
        }
    }
    function unchanged() external pure returns (bytes memory) {
        (bytes memory a, string memory b, bytes memory c) = objects();
        return observe(a, b, c, a, string(a));
    }
    function byteChanged() external pure returns (bytes memory) {
        (bytes memory a, string memory b, bytes memory c) = objects();
        bytes memory aliasA = a; changeA(aliasA);
        return observe(a, b, c, aliasA, string(a));
    }
    function stringChanged() external pure returns (bytes memory) {
        (bytes memory a, string memory b, bytes memory c) = objects(); changeB(b);
        return observe(a, b, c, a, string(a));
    }
    function twoForward() external pure returns (bytes memory) {
        (bytes memory a, string memory b, bytes memory c) = objects(); changeA(a); changeB(b);
        return observe(a, b, c, a, string(a));
    }
    function twoReverse() external pure returns (bytes memory) {
        (bytes memory a, string memory b, bytes memory c) = objects(); changeB(b); changeA(a);
        return observe(a, b, c, a, string(a));
    }
    function sameWrite() external pure returns (bytes memory) {
        (bytes memory a, string memory b, bytes memory c) = objects(); a[0] = 0x11; bytes(b)[0] = 0x61;
        return observe(a, b, c, a, string(a));
    }
    // Supported raw EVM behavior, still OPEN in the fixed-shape heap preparation.
    function headerChange() external pure returns (bytes memory) {
        (bytes memory a, string memory b, bytes memory c) = objects();
        assembly ("memory-safe") { mstore(a, 4) }
        return observe(a, b, c, a, string(a));
    }
    function explicitRevert() external pure {
        (bytes memory a,,) = objects(); changeA(a); revert();
    }
    function boundaries() external pure returns (bytes memory) {
        assembly ("memory-safe") {
            let p0 := mload(0x40)
            let p31 := add(p0, 32)
            let p32 := add(p31, 64)
            let p33 := add(p32, 64)
            mstore(0x40, add(p33, 96))
            mstore(p0, 0)
            mstore(p31, 31)
            mstore(add(p31, 32), 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa5)
            mstore(p32, 32)
            mstore(add(p32, 32), 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
            mstore(p33, 33)
            mstore(add(p33, 32), 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
            mstore(add(p33, 64), 0xffa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5)
            let out := mload(0x40)
            mstore(out, 32)
            mstore(add(out, 32), 512)
            let data := add(out, 64)
            mstore(data, mload(p0))
            mstore(add(data, 32), mload(p31))
            mstore(add(data, 64), mload(p32))
            mstore(add(data, 96), mload(p33))
            mstore(add(data, 128), mload(add(p31, 32)))
            mstore(add(data, 160), mload(add(p32, 32)))
            mstore(add(data, 192), mload(add(p33, 32)))
            mstore(add(data, 224), mload(add(p33, 64)))
            mstore(add(data, 256), p31)
            mstore(add(data, 288), p32)
            mstore(add(data, 320), p33)
            mstore(add(data, 352), mload(0x40))
            mstore(add(data, 384), mload(0x60))
            mstore(add(data, 416), byte(31, mload(add(p31, 32))))
            mstore(add(data, 448), byte(31, mload(add(p32, 32))))
            mstore(add(data, 480), byte(1, mload(add(p33, 64))))
            return(out, 576)
        }
    }
}
