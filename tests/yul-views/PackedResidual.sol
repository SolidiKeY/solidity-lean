// SPDX-License-Identifier: MIT
pragma solidity 0.8.38;
// Finite canonical field/complement evidence only; no assembly admission claim.
contract PackedResidual layout at 7 {
    bool flag; uint16 small; bytes3 data; address who; uint256 other;
    uint256 transient t0; uint256 transient t1; uint256 transient t2;
    uint256 transient t3; uint256 transient t4; uint256 transient t5; uint256 transient t6;
    bool transient txFlag; uint16 transient txSmall; bytes3 transient txData; address transient txWho;
    uint256 constant Z = 0xa5a5a5a5a5a50000000000000000000000000000000000000000000000000000;
    uint256 constant A = 0xa5a5a5a5a5a51234567890123456789012345678901234567890ff00aa123401;
    uint256 constant B = 0x5a5a5a5a5a5aabcdefabcdefabcdefabcdefabcdefabcdefabcd112233beef00;
    constructor() { other = 55; assembly ("memory-safe") { sstore(flag.slot, Z) } }
    function readStored() public view returns (uint256[13] memory r) {
        assembly ("memory-safe") { mstore(r,sload(flag.slot)) mstore(add(r,32),tload(txFlag.slot)) mstore(add(r,352),sload(other.slot)) mstore(add(r,384),sload(99)) }
        r[2] = flag ? 1 : 0; r[3] = small; r[4] = uint256(bytes32(data)); r[5] = uint160(who);
        r[6] = txFlag ? 1 : 0; r[7] = txSmall; r[8] = uint256(bytes32(txData)); r[9] = uint160(txWho); r[10] = other;
    }
    function forward() external returns (uint256[13] memory) {
        assembly ("memory-safe") { sstore(flag.slot,A) tstore(txFlag.slot,A) } return readStored();
    }
    function orderForward() external returns (uint256[13] memory) {
        assembly ("memory-safe") { sstore(flag.slot,A) sstore(flag.slot,B) tstore(txFlag.slot,B) } return readStored();
    }
    function orderReverse() external returns (uint256[13] memory) {
        assembly ("memory-safe") { sstore(flag.slot,B) sstore(flag.slot,A) tstore(txFlag.slot,A) } return readStored();
    }
    function child(bool fail) external { require(msg.sender == address(this)); assembly ("memory-safe") { sstore(flag.slot,B) tstore(txFlag.slot,B) } if (fail) revert(); }
    function innerRevertPrefix() external returns (uint256[13] memory) {
        assembly ("memory-safe") { sstore(flag.slot,A) tstore(txFlag.slot,A) } try this.child(true) {} catch {} return readStored();
    }
    function outerRevertAfterChild() external { assembly ("memory-safe") { sstore(flag.slot,B) tstore(txFlag.slot,B) } this.child(false); revert(); }
    function successAndTransient() external returns (uint256[13] memory) { this.child(false); return readStored(); }
    function typedChanges() external returns (uint256[13] memory) {
        flag = true; small = 0x1234; data = hex"ff00aa"; who = address(0x1234567890123456789012345678901234567890);
        txFlag = true; txSmall = 0x1234; txData = hex"ff00aa"; txWho = address(0x1234567890123456789012345678901234567890); return readStored();
    }
    function dirtyOwned() external returns (uint256[13] memory) {
        assembly ("memory-safe") { sstore(flag.slot,or(and(A,not(255)),2)) } return readStored();
    }
    function staticAttempt() external returns (bool,uint) {
        (bool ok,) = address(this).staticcall{gas:1000000}(abi.encodeCall(this.child,(false)));
        uint raw; assembly ("memory-safe") { raw := sload(flag.slot) } return (ok,raw);
    }
}
