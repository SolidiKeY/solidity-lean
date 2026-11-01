// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.38;
contract ComponentControls {
    uint256 public value;
    constructor() { value = 7; }
    function pair() external pure returns (uint256) {
        assembly ("memory-safe") { mstore(0, add(250, 9)) return(0, 32) }
    }
    function fail() external {
        assembly ("memory-safe") {
            sstore(0, 42)
            mstore(0, shl(240, 0xabcd))
            log0(0, 2)
            revert(0, 2)
        }
    }
    function caught() external {
        assembly ("memory-safe") { mstore(0, 0x11) log0(31, 1) }
        try this.fail() { revert(); }
        catch (bytes memory data) {
            assembly ("memory-safe") { return(add(data, 32), mload(data)) }
        }
    }
}
