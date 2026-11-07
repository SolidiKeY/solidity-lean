// SPDX-License-Identifier: MIT
pragma solidity 0.8.38;

contract MappingTransient {
    mapping(uint256 => uint256) private table;
    uint256 private marker;
    uint16 transient private temp;

    function readState() external view returns (uint256,uint256,uint256,uint256) {
        uint256 raw; assembly ("memory-safe") { raw := sload(table.slot) }
        return (marker,raw,table[1],table[2]);
    }
    function readMap(uint256 key) external view returns (uint256 value,uint256 raw,uint256 slot) {
        assembly ("memory-safe") { mstore(0,key) mstore(32,table.slot) slot := keccak256(0,64) raw := sload(slot) }
        value=table[key];
    }
    function setMap(uint256 key,uint256 value,bool fail) external returns (uint256,uint256,uint256,uint256) {
        marker+=1;
        uint256 slot; uint256 raw;
        assembly ("memory-safe") { mstore(0,key) mstore(32,table.slot) slot := keccak256(0,64) sstore(slot,value) raw := sload(slot) }
        require(!fail,"mapping");
        return (table[key],raw,slot,marker);
    }
    function sameMap(uint256 key) external returns (uint256 raw) {
        assembly ("memory-safe") { mstore(0,key) mstore(32,table.slot) let slot := keccak256(0,64) raw := sload(slot) sstore(slot,raw) }
    }
    function staticMap(uint256 key) external view returns (bool ok,bytes memory data) {
        return address(this).staticcall(abi.encodeCall(this.sameMap,(key)));
    }
    function seed() external returns (uint256 raw) {
        assembly ("memory-safe") { sstore(table.slot,777) raw := sload(table.slot) }
    }
    function childTransient(bool fail) external returns (uint256 typedValue,uint256 raw,uint256 unknown) {
        assembly ("memory-safe") { tstore(temp.slot,0xb6b6abcd) tstore(99,88) }
        require(!fail,"transient child");
        typedValue=temp;
        assembly ("memory-safe") { raw := tload(temp.slot) unknown := tload(99) }
    }
    function transientScenario(bool childReverts,bool outerReverts) external returns
        (uint256 beforeValue,uint256 afterValue,uint256 raw,uint256 unknown,bool ok,bytes memory data,uint256 count)
    {
        marker+=1;
        assembly ("memory-safe") { tstore(temp.slot,0xa5a51234) tstore(99,77) }
        beforeValue=temp;
        (ok,data)=address(this).call(abi.encodeCall(this.childTransient,(childReverts)));
        afterValue=temp;
        assembly ("memory-safe") { raw := tload(temp.slot) unknown := tload(99) }
        require(!outerReverts,"transient outer");
        count=marker;
    }
    function readTransient() external view returns (uint256 typedValue,uint256 raw,uint256 unknown) {
        typedValue=temp;
        assembly ("memory-safe") { raw := tload(temp.slot) unknown := tload(99) }
    }
    function staticProbe() external view returns (bool ok,bytes memory data) {
        return address(this).staticcall(abi.encodeCall(this.childTransient,(false)));
    }
}
