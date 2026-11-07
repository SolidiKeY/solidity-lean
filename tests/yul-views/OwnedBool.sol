pragma solidity 0.8.38;
contract OwnedBool {
    bool flag;
    uint16 small;
    bytes3 data;
    address who;
    uint256 marker;
    constructor() { assembly ("memory-safe") { sstore(0, or(shl(248, 0xab), or(shl(48, 0x1234567890123456789012345678901234567890), or(shl(24, 0xaabbcc), or(shl(8, 0x1234), 2))))) sstore(1, 777) } }
    function snap() public view returns (uint256 truth, uint256 raw, uint16 n, bytes3 b, address a, uint256 m) {
        truth = flag ? 1 : 0;
        assembly ("memory-safe") { raw := sload(0) }
        return (truth, raw, small, data, who, marker);
    }
    function writeThree() external returns (uint256,uint256,uint16,bytes3,address,uint256) { assembly ("memory-safe") { sstore(0, or(and(sload(0), not(255)), 3)) } return snap(); }
    function write255() external returns (uint256,uint256,uint16,bytes3,address,uint256) { assembly ("memory-safe") { sstore(0, or(and(sload(0), not(255)), 255)) } return snap(); }
    function setFalse() external returns (uint256,uint256,uint16,bytes3,address,uint256) { flag=false; return snap(); }
    function setTrue() external returns (uint256,uint256,uint16,bytes3,address,uint256) { flag=true; return snap(); }
    function childFail() external { assembly ("memory-safe") { sstore(0, or(and(sload(0), not(255)), 9)) } revert("owned bool"); }
    function outerFail() external { this.writeThree(); revert("outer"); }
    function staticProbe() external view returns (bool,uint256) { (bool ok, bytes memory reason)=address(this).staticcall(abi.encodeWithSelector(this.writeThree.selector)); return (ok,reason.length); }
}
