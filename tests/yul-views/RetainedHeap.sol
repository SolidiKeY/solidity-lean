// SPDX-License-Identifier: MIT
pragma solidity 0.8.38;
import "HeapResize.sol";

// Retain the actual original ordinary allocation, not ownership inferred from a gap.
contract RetainedHeap is HeapResize {
    function zeroRegrowA4() external pure returns (bytes memory) {
        (bytes memory a, string memory b, bytes memory c) = objects();
        assembly ("memory-safe") { mstore(a, 0) mstore(a, 4) }
        return observeResize(a, b, c, a);
    }
    function zeroRegrowA32() external pure returns (bytes memory) {
        (bytes memory a, string memory b, bytes memory c) = objects();
        assembly ("memory-safe") { mstore(a, 0) mstore(a, 32) }
        return observeResize(a, b, c, a);
    }
    function zeroRegrowString64() external pure returns (bytes memory) {
        (bytes memory a, string memory b, bytes memory c) = objects();
        bytes memory aliasB = bytes(b);
        for (uint i = 0; i < 32; ++i) aliasB[i] = i == 0 ? bytes1(0xff) : bytes1(0x62);
        assembly ("memory-safe") { mstore(b, 0) mstore(b, 64) }
        return observeResize(a, b, c, bytes(b));
    }
    function retainedForward() external pure returns (bytes memory) {
        (bytes memory a, string memory b, bytes memory c) = objects();
        assembly ("memory-safe") { mstore(a, 0) mstore(b, 0) mstore(a, 4) mstore(b, 64) }
        return observeResize(a, b, c, bytes(b));
    }
    function retainedReverse() external pure returns (bytes memory) {
        (bytes memory a, string memory b, bytes memory c) = objects();
        assembly ("memory-safe") { mstore(a, 0) mstore(b, 0) mstore(b, 64) mstore(a, 4) }
        return observeResize(a, b, c, bytes(b));
    }
    function retainedStages() external pure returns (uint, uint, uint, uint, uint, uint) {
        (bytes memory a,,) = objects();
        bytes memory aliasA = a;
        string memory aliasS = string(a);
        assembly ("memory-safe") { mstore(a, 0) }
        uint first = aliasA.length;
        uint second = bytes(aliasS).length;
        assembly ("memory-safe") { mstore(a, 4) }
        return (first, second, aliasA.length, bytes(aliasS).length, uint8(aliasA[3]), uint8(bytes(aliasS)[3]));
    }
    function retainedRevert() external pure {
        (bytes memory a, string memory b,) = objects();
        assembly ("memory-safe") { mstore(a, 0) mstore(b, 0) mstore(a, 4) mstore(b, 64) }
        revert();
    }
}
