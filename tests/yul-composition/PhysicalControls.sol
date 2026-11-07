// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.38;
contract PhysicalA { uint8 private a; }
contract PhysicalB is PhysicalA { uint248 internal b; }
contract PhysicalC is PhysicalA {
    bool internal c;
    struct DiamondInner { bool flag; uint16 small; }
    DiamondInner[2] internal items;
}
contract PhysicalD layout at 42 is PhysicalB, PhysicalC {
    uint248 internal e;
    uint16 internal f;
    uint256 internal marker;
    uint16 transient temp;
    function peek() external view returns (bool logical, uint256 raw) {
        logical = c;
        assembly ("memory-safe") { raw := sload(c.slot) }
    }
    function first() external returns (bool logical, uint256 raw) {
        assembly ("memory-safe") { sstore(c.slot, 0xab000002) raw := sload(c.slot) }
        logical = c;
    }
    function child() external {
        assembly ("memory-safe") { sstore(c.slot, 0xcd000003) }
    }
    function outer() external {
        assembly ("memory-safe") { sstore(c.slot, 0xab000002) }
        this.child();
        assembly ("memory-safe") { mstore(0, sload(c.slot)) revert(0,32) }
    }
}
