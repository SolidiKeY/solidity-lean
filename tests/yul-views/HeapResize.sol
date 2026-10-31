// SPDX-License-Identifier: MIT
pragma solidity 0.8.38;
import "HeapBytes.sol";

// Separate resize observations; inherited frozen fixture remains unchanged.
contract HeapResize is HeapBytes {
    function observeResize(bytes memory a, string memory b, bytes memory c, bytes memory aliasA)
        internal pure returns (bytes memory) {
        string memory aliasS = string(aliasA);
        uint lenA = aliasA.length;
        uint lenS = bytes(aliasS).length;
        uint8 firstA = lenA == 0 ? 0 : uint8(aliasA[0]);
        uint8 firstS = lenS == 0 ? 0 : uint8(bytes(aliasS)[0]);
        assembly ("memory-safe") {
            let out := mload(0x40)
            mstore(out, 32)
            mstore(add(out, 32), 640)
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
            mstore(add(data, 384), lenA)
            mstore(add(data, 416), lenS)
            mstore(add(data, 448), firstA)
            mstore(add(data, 480), firstS)
            mstore(add(data, 512), eq(aliasA, aliasS))
            mstore(add(data, 544), mload(add(aliasA, 32)))
            mstore(add(data, 576), mload(aliasA))
            mstore(add(data, 608), byte(1, mload(add(a, 32))))
            return(out, 704)
        }
    }
    function sameHeader() external pure returns (bytes memory) {
        (bytes memory a, string memory b, bytes memory c) = objects();

        return observeResize(a, b, c, a);
    }
    function grow3to4() external pure returns (bytes memory) {
        (bytes memory a, string memory b, bytes memory c) = objects();
        assembly ("memory-safe") { mstore(a, 4) }
        return observeResize(a, b, c, a);
    }
    function shrink3to1() external pure returns (bytes memory) {
        (bytes memory a, string memory b, bytes memory c) = objects();
        assembly ("memory-safe") { mstore(a, 1) }
        return observeResize(a, b, c, a);
    }
    function shrink3to0() external pure returns (bytes memory) {
        (bytes memory a, string memory b, bytes memory c) = objects();
        assembly ("memory-safe") { mstore(a, 0) }
        return observeResize(a, b, c, a);
    }
    function grow3to32() external pure returns (bytes memory) {
        (bytes memory a, string memory b, bytes memory c) = objects();
        assembly ("memory-safe") { mstore(a, 32) }
        return observeResize(a, b, c, a);
    }
    function string33to32() external pure returns (bytes memory) {
        (bytes memory a, string memory b, bytes memory c) = objects();
        bytes memory aliasB = bytes(b);
        for (uint i = 0; i < 32; ++i) aliasB[i] = i == 0 ? bytes1(0xff) : bytes1(0x62);
        assembly ("memory-safe") { mstore(b, 32) }
        return observeResize(a, b, c, bytes(b));
    }
    function bucket31to32() external pure returns (bytes memory) {
        (bytes memory a, string memory b, bytes memory c) = objects();
        assembly ("memory-safe") {
            mstore(b, 31)
            mstore(add(b, 32), 0x11111111111111111111111111111111111111111111111111111111111111a5)
            mstore(add(b, 64), 0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5)
            mstore(b, 32)
        }
        return observeResize(a, b, c, bytes(b));
    }
    function shrink33to31() external pure returns (bytes memory) {
        (bytes memory a, string memory b, bytes memory c) = objects();
        assembly ("memory-safe") {
            mstore(add(b, 32), 0x1111111111111111111111111111111111111111111111111111111111111111)
            mstore(add(b, 64), 0x11a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5)
            mstore(b, 31)
        }
        return observeResize(a, b, c, bytes(b));
    }
    function grow33to64() external pure returns (bytes memory) {
        (bytes memory a, string memory b, bytes memory c) = objects();
        assembly ("memory-safe") { mstore(b, 64) }
        return observeResize(a, b, c, bytes(b));
    }
    function beyondFootprint() external pure returns (bytes memory) {
        (bytes memory a, string memory b, bytes memory c) = objects();
        // Open in the selected-footprint preparation, not a Yul refusal.
        assembly ("memory-safe") { mstore(b, 65) }
        return observeResize(a, b, c, bytes(b));
    }
    function explicitRevertResize() external pure {
        (bytes memory a,,) = objects();
        assembly ("memory-safe") { mstore(a, 4) }
        revert();
    }
}
