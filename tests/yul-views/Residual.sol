// SPDX-License-Identifier: MIT
pragma solidity 0.8.38;

// Fixed unowned-slot companion evidence only, not a Yul correspondence proof.
contract Residual layout at 7 {
    bool private first;
    bool private second;
    bool transient private txFlag;
    function seedPrefix() private {
        assembly ("memory-safe") {
            sstore(first.slot, 0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a50000)
            sstore(99, 165)
            sstore(100, 165)
            tstore(99, 165)
            sstore(99, 41)
            sstore(99, 42)
        }
        first = true;
    }
    function child(bool fail) external {
        require(msg.sender == address(this));
        second = true; txFlag = true;
        assembly ("memory-safe") { sstore(99, 43) tstore(99, 7) }
        if (fail) revert();
    }
    function readStored() public view returns (uint raw, uint residual, bool flag, uint transientResidual, uint sentinel) {
        flag = txFlag;
        assembly ("memory-safe") {
            raw := sload(first.slot)
            residual := sload(99)
            transientResidual := tload(99)
            sentinel := sload(100)
        }
    }
    function innerRevertPrefix() external returns (uint, uint, bool, uint, uint) {
        seedPrefix();
        try this.child(true) {} catch {}
        return readStored();
    }
    function outerRevertAfterChild() external {
        seedPrefix();
        this.child(false);
        revert();
    }
    function successAndTransient() external returns (uint, uint, bool, uint, uint) {
        seedPrefix();
        this.child(false);
        return readStored();
    }
}
