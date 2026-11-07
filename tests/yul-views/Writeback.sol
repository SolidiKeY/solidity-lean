// SPDX-License-Identifier: MIT
pragma solidity 0.8.38;

// Reference evidence only: not Lean admission or a writeback correspondence proof.
contract Writeback layout at 7 {
    bool private first;
    bool private second;
    bool transient private txFlag;

    function seed() private {
        assembly ("memory-safe") {
            sstore(first.slot, 0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a50000)
        }
    }
    function raw() private view returns (uint x) {
        assembly ("memory-safe") { x := sload(first.slot) }
    }
    function unchangedDefault() external returns (uint, bool) {
        seed(); first = false;
        return (raw(), first);
    }
    function changedAndDisjoint() external returns (uint, bool, bool) {
        seed(); first = true; second = true;
        return (raw(), first, second);
    }
    function repeated() external returns (uint, bool, bool) {
        seed(); first = true; first = true;
        return (raw(), first, second);
    }
    // Required dirty representation survives on the reference EVM. The canonical
    // Lean preparation decoder's unsupported result is NOT an EVM no-op/revert.
    function rawNoncanonical() external returns (uint, bool) {
        seed();
        assembly ("memory-safe") { sstore(first.slot, or(sload(first.slot), 2)) }
        return (raw(), first);
    }
    function childWrites(bool fail) external {
        require(msg.sender == address(this));
        second = true; txFlag = true;
        if (fail) revert();
    }
    function innerRevertPrefix() external returns (uint, bool) {
        seed(); first = true;
        try this.childWrites(true) {} catch {}
        return (raw(), txFlag);
    }
    function outerRevertAfterChild() external {
        seed(); first = true;
        this.childWrites(false);
        revert();
    }
    function successAndTransient() external returns (uint, bool) {
        seed(); first = true;
        this.childWrites(false);
        return (raw(), txFlag);
    }
    function readStored() external view returns (uint, bool) { return (raw(), txFlag); }
}
