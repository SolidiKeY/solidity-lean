// SPDX-License-Identifier: MIT
pragma solidity 0.8.38;
contract NestedMapping {
    mapping(uint256 => mapping(uint256 => uint256)) private table;
    uint256 private marker;
    function state() external view returns (uint256,uint256,uint256,uint256,uint256) {
        uint256 raw; assembly ("memory-safe") { raw := sload(table.slot) }
        return (marker,raw,table[1][2],table[1][3],table[2][2]);
    }
    function read(uint256 outer,uint256 inner) public view returns (uint256,uint256,uint256,uint256) {
        uint256 parent; uint256 slot; uint256 raw;
        assembly ("memory-safe") {
            mstore(0,outer) mstore(32,table.slot) parent := keccak256(0,64)
            mstore(0,inner) mstore(32,parent) slot := keccak256(0,64) raw := sload(slot)
        }
        return (table[outer][inner],raw,parent,slot);
    }
    function put(uint256 outer,uint256 inner,uint256 value,bool fail) external returns (uint256,uint256,uint256,uint256) {
        marker+=1;
        assembly ("memory-safe") {
            mstore(0,outer) mstore(32,table.slot) let parent := keccak256(0,64)
            mstore(0,inner) mstore(32,parent) sstore(keccak256(0,64),value)
        }
        require(!fail,"nested mapping");
        return read(outer,inner);
    }
    function same(uint256 outer,uint256 inner) external returns (uint256 raw) {
        assembly ("memory-safe") {
            mstore(0,outer) mstore(32,table.slot) let parent := keccak256(0,64)
            mstore(0,inner) mstore(32,parent) let slot := keccak256(0,64)
            raw := sload(slot) sstore(slot,raw)
        }
    }
    function probe() external view returns (bool,bytes memory) {
        return address(this).staticcall(abi.encodeCall(this.same,(1,2)));
    }
    function seed() external returns (uint256 raw) {
        assembly ("memory-safe") { sstore(table.slot,165) sstore(79,4243) raw := sload(table.slot) }
    }
}
