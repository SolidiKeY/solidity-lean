// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.38;

// Finite canonical-rethrow control, separate from compiler correctness.
contract ObservedNativeRethrowControls {
    uint256 public marker;

    function checkMarker(uint256 expected) external view { require(marker == expected); }

    function child(uint256 mode) external {
        marker = 99;
        assembly ("memory-safe") { tstore(0, 0x33) mstore(0, 0x77) log0(31, 1) }
        this.checkMarker(99);
        if (mode == 2) { assert(false); }
        if (mode == 1) { assembly ("memory-safe") { revert(0, 0) } }
        if (mode == 3) { assembly ("memory-safe") { mstore(0, 0xaabb) revert(30, 2) } }
        assembly ("memory-safe") { mstore(0, 0xdead) revert(30, 2) }
    }

    function rethrowCaught(uint256 mode) internal {
        marker = 7;
        assembly ("memory-safe") { tstore(0, 0x11) mstore(0, 0x55) log0(31, 1) }
        try this.child(mode) { revert(); }
        catch (bytes memory data) {
            marker = 8;
            assembly ("memory-safe") { tstore(0, 0x22) mstore(0, 0x66) log0(31, 1) }
            this.checkMarker(8);
            assembly ("memory-safe") { revert(add(data, 32), mload(data)) }
        }
    }
    function dead() external { rethrowCaught(0); }
    function empty() external { rethrowCaught(1); }
    function panicPayload() external { rethrowCaught(2); }
    function wrongPayload() external { rethrowCaught(3); }

    function alwaysRevert() external pure {
        assembly ("memory-safe") { mstore(0, 0xdead) revert(30, 2) }
    }

    function good() external pure {
        assembly ("memory-safe") { mstore(0, 0xbeef) return(30, 2) }
    }
    function success() external {
        marker = 7;
        assembly ("memory-safe") { mstore(0, 0x55) log0(31, 1) }
        try this.good() {
            assembly ("memory-safe") { mstore(0, 0xbeef) return(30, 2) }
        } catch (bytes memory data) {
            assembly ("memory-safe") { revert(add(data, 32), mload(data)) }
        }
    }
}
