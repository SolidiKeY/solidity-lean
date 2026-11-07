// SPDX-License-Identifier: MIT
pragma solidity 0.8.38;
import "HeapBytes.sol";

// Finite physical allocation/retention evidence, not source admission/adequacy.
contract RetainedAllocation is HeapBytes {
    uint public marker = 777;
    function fresh() internal pure returns (string memory d) {
        assembly ("memory-safe") {
            d := mload(0x40)
            mstore(0x40, add(d, 64))
            mstore(d, 4)
            mstore(add(d, 32), 0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5)
            mstore8(add(d, 32), 0xfe)
            mstore8(add(d, 33), 0)
            mstore8(add(d, 34), 0xfd)
            mstore8(add(d, 35), 0xfc)
        }
    }
    function snapshot(bytes memory a, string memory b, bytes memory c, string memory d,
        bytes memory aliasA, string memory aliasS, uint tag) internal view returns (bytes memory) {
        bytes memory aliasD = bytes(d);
        assembly ("memory-safe") {
            let out := mload(0x40)
            mstore(out, 32)
            mstore(add(out, 32), 928)
            let data := add(out, 64)
            mstore(data, mload(a))
            mstore(add(data, 32), mload(add(a, 32)))
            mstore(add(data, 64), a)
            mstore(add(data, 96), mload(b))
            mstore(add(data, 128), mload(add(b, 32)))
            mstore(add(data, 160), mload(add(b, 64)))
            mstore(add(data, 192), b)
            mstore(add(data, 224), mload(c))
            mstore(add(data, 256), mload(add(c, 32)))
            mstore(add(data, 288), c)
            mstore(add(data, 320), mload(d))
            mstore(add(data, 352), mload(add(d, 32)))
            mstore(add(data, 384), d)
            mstore(add(data, 416), mload(0x40))
            mstore(add(data, 448), mload(0x60))
            mstore(add(data, 480), mload(add(a, 64)))
            mstore(add(data, 512), mload(add(b, 96)))
            mstore(add(data, 544), mload(add(c, 64)))
            mstore(add(data, 576), byte(0, mload(add(aliasA, 32))))
            mstore(add(data, 608), byte(0, mload(add(aliasS, 32))))
            mstore(add(data, 640), byte(0, mload(add(aliasD, 32))))
            mstore(add(data, 672), eq(a, aliasA))
            mstore(add(data, 704), eq(a, aliasS))
            mstore(add(data, 736), eq(d, aliasD))
            mstore(add(data, 768), mload(aliasA))
            mstore(add(data, 800), mload(aliasS))
            mstore(add(data, 832), mload(aliasD))
            mstore(add(data, 864), sload(marker.slot))
            mstore(add(data, 896), tag)
            return(out, 992)
        }
    }
    function forward() external view returns (bytes memory) {
        (bytes memory a, string memory b, bytes memory c) = objects();
        bytes memory aliasA = a;
        string memory aliasS = string(a);
        assembly ("memory-safe") { mstore(a, 0) }
        string memory d = fresh();
        assembly ("memory-safe") { mstore(a, 4) }
        return snapshot(a, b, c, d, aliasA, aliasS, 1);
    }
    function reverse() external view returns (bytes memory) {
        (bytes memory a, string memory b, bytes memory c) = objects();
        string memory d = fresh();
        assembly ("memory-safe") { mstore(a, 0) mstore(a, 4) }
        return snapshot(a, b, c, d, a, string(a), 2);
    }
    function newRegrow() external view returns (bytes memory) {
        (bytes memory a, string memory b, bytes memory c) = objects();
        assembly ("memory-safe") { mstore(a, 0) }
        string memory d = fresh();
        assembly ("memory-safe") { mstore(a, 4) mstore(d, 0) mstore(d, 8) }
        return snapshot(a, b, c, d, a, string(a), 3);
    }
    function stages() external pure returns (uint, uint, uint, uint, uint, uint, uint) {
        (bytes memory a,,) = objects();
        bytes memory aliasA = a;
        string memory aliasS = string(a);
        assembly ("memory-safe") { mstore(a, 0) }
        uint first = aliasA.length;
        uint second = bytes(aliasS).length;
        string memory d = fresh();
        assembly ("memory-safe") { mstore(a, 4) }
        return (first, second, aliasA.length, bytes(aliasS).length, uint8(aliasA[3]), uint8(bytes(aliasS)[3]), bytes(d).length);
    }
    function panicAlias() external pure returns (uint) {
        (bytes memory a,,) = objects();
        assembly ("memory-safe") { mstore(a, 0) }
        string memory d = fresh();
        return uint8(a[0]) + bytes(d).length;
    }
    function fail() external {
        marker = 888;
        (bytes memory a,,) = objects();
        assembly ("memory-safe") { mstore(a, 0) }
        string memory d = fresh();
        assembly ("memory-safe") { mstore(a, 4) mstore(d, 0) }
        revert("allocation");
    }
    function staticProbe() external view returns (bool, uint, uint) {
        (bool ok, bytes memory data) = address(this).staticcall(abi.encodeWithSelector(this.fail.selector));
        return (ok, data.length, marker);
    }
    function untouched() external view returns (bytes memory) {
        (bytes memory a, string memory b, bytes memory c) = objects();
        return snapshot(a, b, c, fresh(), a, string(a), 0);
    }
}
