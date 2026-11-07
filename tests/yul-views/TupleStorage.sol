// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.38;
contract TupleStorage {
    struct Node { uint16 stamp; uint16[] xs; }
    Node[] nodes;
    uint256 guard;
    uint256 marker;
    constructor() {
        assembly ("memory-safe") {
            sstore(nodes.slot,2)
            sstore(guard.slot,777)
            mstore(0,nodes.slot)
            let h:=keccak256(0,32)
            sstore(h,add(shl(240,1),12))
            sstore(add(h,1),2)
            sstore(add(h,2),add(shl(240,1),13))
            sstore(add(h,3),1)
            mstore(0,add(h,1))
            sstore(keccak256(0,32),add(shl(240,1),add(shl(32,77),add(shl(16,88),77))))
            mstore(0,add(h,3))
            sstore(keccak256(0,32),55)
        }
    }
    function snap() public view returns (uint256[8] memory out) {
        assembly ("memory-safe") {
            mstore(0,nodes.slot)
            let h:=keccak256(0,32)
            mstore(out,sload(nodes.slot))
            mstore(add(out,32),sload(add(h,1)))
            mstore(0,add(h,1))
            mstore(add(out,64),sload(keccak256(0,32)))
            mstore(add(out,96),sload(h))
            mstore(add(out,128),sload(add(h,3)))
            mstore(0,add(h,3))
            mstore(add(out,160),sload(keccak256(0,32)))
            mstore(add(out,192),sload(guard.slot))
            mstore(add(out,224),sload(marker.slot))
        }
    }
    // This callee has NO storage-reference parameter or local.
    function suspend() internal {
        assembly ("memory-safe") {
            sstore(nodes.slot,0)
            mstore(0,nodes.slot)
            sstore(add(keccak256(0,32),1),3)
        }
        marker=1;
    }
    function refs() internal view returns (Node storage r, uint16[] storage a, uint16[] storage b) {
        r=nodes[0]; a=r.xs; b=r.xs;
    }
    function run() external returns (uint256[8] memory out, bytes memory reason) {
        (Node storage r,uint16[] storage a,uint16[] storage b)=refs();
        suspend();
        (bool ok,bytes memory data)=address(this).call(abi.encodeCall(this.childFail,()));
        out=[nodes.length,a.length,uint256(b[2]),uint256(r.stamp),marker,guard,ok?uint256(1):uint256(0),snap()[2]];
        reason=data;
    }
    function restore() external returns (uint256[8] memory) {
        assembly ("memory-safe") { sstore(nodes.slot,2) }
        return snap();
    }
    function childFail() external {
        assembly ("memory-safe") {
            mstore(0,nodes.slot)
            let h:=keccak256(0,32)
            sstore(add(h,1),4)
            mstore(0,add(h,1))
            sstore(keccak256(0,32),177)
            mstore(0,add(h,3))
            sstore(keccak256(0,32),222)
        }
        marker=999;
        revert("child");
    }
    function childSuccess() external {
        assembly ("memory-safe") {
            mstore(0,nodes.slot)
            let h:=keccak256(0,32)
            sstore(add(h,1),4)
            mstore(0,add(h,3))
            sstore(keccak256(0,32),333)
        }
        marker=999;
    }
    function successThenOuterRevert() external {
        uint16[] storage held=nodes[0].xs;
        suspend();
        this.childSuccess();
        require(held.length==4,"length");
        revert("outer");
    }
    function attemptWrite() external { suspend(); }
    function staticProbe() external view returns (uint256[2] memory out) {
        (bool ok,bytes memory reason)=address(this).staticcall(abi.encodeCall(this.attemptWrite,()));
        out=[ok?uint256(1):uint256(0),reason.length];
    }
    function bounds() external view returns (uint16) { return nodes[2].xs[0]; }
}
