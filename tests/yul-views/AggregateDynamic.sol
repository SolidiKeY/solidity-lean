// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.38;
contract AggregateDynamic {
    struct Node { uint16 stamp; uint16[] xs; int24[] ys; bool[] bs; }
    Node[] nodes;
    uint16[][] grid;
    uint256 marker;
    constructor() {
        assembly ("memory-safe") {
            sstore(nodes.slot, 2)
            sstore(grid.slot, 2)
            mstore(0, nodes.slot)
            let h := keccak256(0, 32)
            sstore(h, add(shl(240, 1), 12))
            sstore(add(h, 1), 2)
            sstore(add(h, 2), 1)
            sstore(add(h, 3), 1)
            sstore(add(h, 4), add(shl(240, 1), 13))
            sstore(add(h, 5), 1)
            mstore(0, add(h, 1))
            sstore(keccak256(0, 32), add(shl(240, 1), add(shl(32, 99), add(shl(16, 88), 77))))
            mstore(0, add(h, 2))
            sstore(keccak256(0, 32), add(shl(240, 1), 0xffffff))
            mstore(0, add(h, 3))
            sstore(keccak256(0, 32), add(shl(240, 1), 1))
            mstore(0, add(h, 5))
            sstore(keccak256(0, 32), 55)
            mstore(0, grid.slot)
            let g := keccak256(0, 32)
            sstore(g, 1)
            sstore(add(g, 1), 1)
            mstore(0, g)
            sstore(keccak256(0, 32), add(shl(240, 1), 33))
            mstore(0, add(g, 1))
            sstore(keccak256(0, 32), add(shl(240, 1), 44))
        }
    }
    function snap() public view returns (uint256[15] memory out) {
        assembly ("memory-safe") {
            mstore(0, nodes.slot)
            let h := keccak256(0, 32)
            mstore(0, grid.slot)
            let g := keccak256(0, 32)
            mstore(out, sload(nodes.slot))
            mstore(add(out,32),sload(grid.slot))
            mstore(add(out,64),sload(marker.slot))
            mstore(add(out,96),sload(h))
            mstore(add(out,128),sload(add(h,1)))
            mstore(0,add(h,1))
            mstore(add(out,160),sload(keccak256(0,32)))
            mstore(0,add(h,2))
            mstore(add(out,192),sload(keccak256(0,32)))
            mstore(0,add(h,3))
            mstore(add(out,224),sload(keccak256(0,32)))
            mstore(add(out,256),sload(add(h,4)))
            mstore(add(out,288),sload(g))
            mstore(add(out,320),sload(add(g,1)))
            mstore(0,g)
            mstore(add(out,352),sload(keccak256(0,32)))
            mstore(0,add(g,1))
            mstore(add(out,384),sload(keccak256(0,32)))
            mstore(add(out,416),sload(add(h,5)))
            mstore(0,add(h,5))
            mstore(add(out,448),sload(keccak256(0,32)))
        }
    }
    function retainedAlias() external returns (uint256[6] memory out) {
        Node storage r=nodes[0]; uint16[] storage a=r.xs; uint16[] storage b=r.xs;
        assembly ("memory-safe") { sstore(nodes.slot,0) sstore(a.slot,3) }
        marker=77;
        out=[nodes.length,a.length,b[2],uint256(r.stamp),uint256(uint24(r.ys[0])),marker];
    }
    function restore() external returns (uint256[15] memory) {
        assembly ("memory-safe") { sstore(nodes.slot,2) }
        return snap();
    }
    function innerShrink() external returns (uint256[15] memory) {
        uint16[] storage a=nodes[0].xs;
        assembly ("memory-safe") { sstore(a.slot,0) }
        return snap();
    }
    function innerRegrow() external returns (uint256[15] memory) {
        uint16[] storage a=nodes[0].xs;
        assembly ("memory-safe") { sstore(a.slot,3) }
        a[1]=123;
        return snap();
    }
    function typed() external view returns (uint256[9] memory) {
        return [nodes[0].xs.length,uint256(nodes[0].xs[0]),uint256(nodes[0].xs[1]),uint256(nodes[0].xs[2]),
            uint256(int256(nodes[0].ys[0])),nodes[0].bs[0]?uint256(1):uint256(0),uint256(grid[0][0]),uint256(grid[1][0]),uint256(nodes[1].xs[0])];
    }
    function failAfterWrite() external { marker=999; nodes[1].xs[0]=222; revert("aggregate"); }
    function bounds() external view returns (uint16) { return nodes[2].xs[0]; }
    function staticProbe() external view returns (bool ok) { (ok,)=address(this).staticcall(abi.encodeCall(this.innerShrink,())); }
}
