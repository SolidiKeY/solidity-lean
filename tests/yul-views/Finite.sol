// SPDX-License-Identifier: MIT
pragma solidity 0.8.38;

// Reference observations for a finite registration, not whole-store/Yul admission.
contract Finite layout at 7 {
    bool private flag;
    uint16 private small;
    uint256 private wide;
    uint8 private other;
    bool transient private txFlag;

    function seed() private {
        assembly ("memory-safe") {
            sstore(flag.slot, 0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5000000)
            sstore(wide.slot, 0)
            sstore(other.slot, 0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a537)
            sstore(99, 0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5)
        }
    }
    function readStored() public view returns (uint, uint, bool, uint16, uint8, uint, uint, bool) {
        uint raw; uint rawOther; uint residual;
        assembly ("memory-safe") { raw := sload(flag.slot) rawOther := sload(other.slot) residual := sload(99) }
        return (raw, wide, flag, small, other, rawOther, residual, txFlag);
    }
    function unchangedDefaults() external returns (uint, uint, bool, uint16, uint8, uint, uint, bool) {
        seed(); flag = false; small = 0; wide = 0; return readStored();
    }
    function forwardChanges() external returns (uint, uint, bool, uint16, uint8, uint, uint, bool) {
        seed(); flag = true; small = 0x1234; wide = 0x112233; return readStored();
    }
    function reverseChanges() external returns (uint, uint, bool, uint16, uint8, uint, uint, bool) {
        seed(); wide = 0x112233; small = 0x1234; flag = true; return readStored();
    }
    function repeatedChanges() external returns (uint, uint, bool, uint16, uint8, uint, uint, bool) {
        seed(); flag = true; small = 0x1234; wide = 0x112233;
        flag = true; small = 0x1234; wide = 0x112233; return readStored();
    }
    // This dirty value remains observable; canonical decoder None is not a refusal.
    function dirtyOwned() external returns (uint, uint, bool, uint16, uint8, uint, uint, bool) {
        seed(); assembly ("memory-safe") { sstore(flag.slot, or(sload(flag.slot), 2)) }
        return readStored();
    }
    function child(bool fail) external {
        require(msg.sender == address(this));
        small = 0x1234; wide = 0x112233; txFlag = true;
        if (fail) revert();
    }
    function innerRevertPrefix() external returns (uint, uint, bool, uint16, uint8, uint, uint, bool) {
        seed(); flag = true; try this.child(true) {} catch {} return readStored();
    }
    function outerRevertAfterChild() external {
        seed(); flag = true; this.child(false); revert();
    }
    function successAndTransient() external returns (uint, uint, bool, uint16, uint8, uint, uint, bool) {
        seed(); flag = true; this.child(false); return readStored();
    }
}
