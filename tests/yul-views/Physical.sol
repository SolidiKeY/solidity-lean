// SPDX-License-Identifier: MIT
pragma solidity 0.8.38;

// Reference-only controls. No claim of Lean frontend admission.
contract Physical {
    struct Heterogeneous { int8 signedValue; bytes2 pair; address owner; int128 wide; bool enabled; }
    Heterogeneous private heterogeneous;
    uint24[12] private fixedArray;
    function heterogeneousPacking() external returns (uint first, uint second) {
        assembly ("memory-safe") {
            sstore(heterogeneous.slot, 0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5)
            sstore(add(heterogeneous.slot, 1), 0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5)
        }
        heterogeneous.signedValue = -1;
        heterogeneous.pair = 0x1234;
        heterogeneous.owner = address(0x112233);
        heterogeneous.wide = -2;
        heterogeneous.enabled = true;
        assembly ("memory-safe") { first := sload(heterogeneous.slot) second := sload(add(heterogeneous.slot, 1)) }
    }
    function fixedArrayPacking() external returns (uint first, uint second) {
        assembly ("memory-safe") {
            sstore(fixedArray.slot, 0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5)
            sstore(add(fixedArray.slot, 1), 0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5)
        }
        for (uint i = 0; i < 12; ++i) fixedArray[i] = uint24(i + 1);
        assembly ("memory-safe") { first := sload(fixedArray.slot) second := sload(add(fixedArray.slot, 1)) }
    }
    bool public flag;
    struct PackedScalars { int8 signedValue; bytes2 pair; bool enabled; }
    PackedScalars private packed;
    function() external returns (uint) private callback;
    function packedScalarFields() external returns (uint raw) {
        assembly ("memory-safe") { sstore(packed.slot, 0x556600000000) }
        packed.signedValue = -1;
        packed.pair = 0x1234;
        packed.enabled = true;
        assembly ("memory-safe") { raw := sload(packed.slot) }
    }
    function externalFunctionPacking() external returns (bool) {
        callback = this.wordRoundtrip;
        uint raw;
        assembly ("memory-safe") { raw := sload(callback.slot) }
        uint expected = (uint(uint160(address(this))) << 32) | uint32(this.wordRoundtrip.selector);
        return raw == expected;
    }
    function wordRoundtrip() external pure returns (uint x) {
        assembly ("memory-safe") { mstore(0x80, 0x12345678) x := mload(0x80) }
    }
    function lowByte() external pure returns (uint x) {
        assembly ("memory-safe") {
            mstore(0x80, 0)
            mstore8(0x9f, 0xabcd)
            x := mload(0x80)
        }
    }
    function overlapRight() external pure returns (uint x) {
        assembly ("memory-safe") {
            mstore(0x80, 0x000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f)
            mcopy(0x82, 0x80, 6)
            x := shr(176, mload(0x80))
        }
    }
    function overlapLeft() external pure returns (uint x) {
        assembly ("memory-safe") {
            mstore(0x80, 0x000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f)
            mcopy(0x80, 0x82, 6)
            x := shr(176, mload(0x80))
        }
    }
    function calldataTail() external pure returns (uint x) {
        assembly ("memory-safe") {
            calldatacopy(0x80, calldatasize(), 32)
            x := or(mload(0x80), calldataload(calldatasize()))
        }
    }
    function emptyHash() external pure returns (uint x) {
        assembly ("memory-safe") { x := keccak256(0, 0) }
    }
    function dirtyLocal() external pure returns (uint raw, uint cleaned) {
        uint8 small;
        assembly ("memory-safe") { small := 0x123456 raw := small }
        cleaned = small;
    }
    function dirtyBool() external pure returns (uint raw, bool cleaned) {
        bool value;
        assembly ("memory-safe") { value := 2 raw := value }
        cleaned = value;
    }
    function dirtyStorageBool() external returns (uint raw, bool logical) {
        assembly ("memory-safe") { sstore(flag.slot, 2) raw := sload(flag.slot) }
        logical = flag;
    }
    function residualSlots() external returns (uint x) {
        assembly ("memory-safe") {
            sstore(999, 42)
            tstore(999, 7)
            x := add(sload(999), tload(999))
        }
    }
    struct NestedFixed { uint24[12] array; Heterogeneous inner; }
    NestedFixed private nested;
    uint private nestedSentinel;
    Heterogeneous[3] private many;
    uint private manySentinel;
    function nestedFixedWords() external returns (uint[5] memory out) {
        out = [uint(0), 0, 0, 0, 0];
        assembly ("memory-safe") {
            for { let i := 0 } lt(i, 5) { i := add(i, 1) } {
                sstore(add(nested.slot, i), 0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5)
            }
        }
        for (uint i = 0; i < 12; ++i) nested.array[i] = uint24(i + 1);
        nested.inner.signedValue = -1;
        nested.inner.pair = 0x1020;
        nested.inner.owner = address(0x112233);
        nested.inner.wide = -2;
        nested.inner.enabled = true;
        for (uint i = 0; i < 5; ++i) {
            uint w;
            assembly ("memory-safe") { w := sload(add(nested.slot, i)) }
            out[i] = w;
        }
    }
    function structArrayWords() external returns (uint[7] memory out) {
        out = [uint(0), 0, 0, 0, 0, 0, 0];
        assembly ("memory-safe") {
            for { let i := 0 } lt(i, 7) { i := add(i, 1) } {
                sstore(add(many.slot, i), 0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5)
            }
        }
        for (uint i = 0; i < 3; ++i) {
            many[i].signedValue = -1 - int8(uint8(i));
            many[i].pair = bytes2((uint16(16 + i) << 8) | uint16(32 + i));
            many[i].owner = address(uint160(0x112233 + i));
            many[i].wide = -2 - int128(uint128(i));
            many[i].enabled = i % 2 == 0;
        }
        for (uint i = 0; i < 7; ++i) {
            uint w;
            assembly ("memory-safe") { w := sload(add(many.slot, i)) }
            out[i] = w;
        }
    }

}
