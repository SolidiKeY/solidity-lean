// SPDX-License-Identifier: MIT
pragma solidity 0.8.38;

// Finite external controls, not frontend admission or compiler adequacy.
contract ResidualMemory {
    uint256 private marker;
    function readState() external view returns (uint256) { return marker; }
    function rawSuccess() external pure {
        assembly ("memory-safe") { mstore(0, 0xdead77) return(29, 3) }
    }
    function rawRevert() external pure {
        assembly ("memory-safe") { mstore(0, 0xcafe88) revert(29, 3) }
    }
    function _copy(bytes memory b, bytes4 selector, bool shrink)
        internal view returns (bytes32 raw, bool ok, bool freeSame, uint256 returnedSize)
    {
        uint256 beforeFree;
        uint256 afterFree;
        assembly ("memory-safe") {
            mstore(add(b,32), 0x112233a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5)
            beforeFree := mload(64)
            if shrink { mstore(b,0) }
            mstore(0,selector)
            let destination := add(b,35)
            if shrink { destination := add(b,32) }
            ok := staticcall(100000,address(),0,4,destination,7)
            returnedSize := returndatasize()
            raw := mload(add(b,32))
            if shrink { mstore(b,3) }
            afterFree := mload(64)
        }
        freeSame = beforeFree == afterFree;
    }
    function touch(bool shrink, bool childReverts, bool outerReverts)
        external returns (bytes memory b, bytes memory aliasView, bytes32 raw, bool ok, bool freeSame, uint256 returnedSize)
    {
        marker += 1;
        b = new bytes(3);
        aliasView = b;
        bytes4 selector = childReverts ? this.rawRevert.selector : this.rawSuccess.selector;
        (raw,ok,freeSame,returnedSize) = _copy(b,selector,shrink);
        require(!outerReverts,"residual");
    }
    function staticProbe() external view returns (bool ok, bytes memory data) {
        return address(this).staticcall(abi.encodeCall(this.touch,(false,false,false)));
    }
    function indexAt(uint256 index) external returns (bytes1) {
        marker += 1;
        bytes memory b = new bytes(3);
        b[0]=0x11; b[1]=0x22; b[2]=0x33;
        return b[index];
    }
}
