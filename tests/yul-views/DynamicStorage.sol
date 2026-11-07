// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.38;
contract DynamicBase { uint8 private a; function setA() internal { a=17; } }
contract DynamicStorage is DynamicBase layout at 42 {
    uint248 n;
    uint256[] xs;
    uint16 mid;
    uint256[] ys;
    uint256 marker;
    uint16 transient temp;
    constructor() {
        marker=55;
        assembly ("memory-safe") {
            sstore(44,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc0000)
            sstore(47,999)
        }
    }
    function readAll() public view returns(uint256[22] memory out) {
        uint256[] storage left=xs; uint256[] storage right=xs;
        out[0]=left.length;out[1]=right.length;out[2]=ys.length;
        if(left.length>0)out[3]=left[0];if(right.length>1)out[4]=right[1];
        if(ys.length>0)out[5]=ys[0];out[6]=marker;out[7]=mid;out[8]=temp;
        assembly ("memory-safe") {
            mstore(0,43) let hx:=keccak256(0,32)
            mstore(0,45) let hy:=keccak256(0,32)
            mstore(add(out,288),sload(42)) mstore(add(out,320),sload(43))
            mstore(add(out,352),sload(44)) mstore(add(out,384),sload(45))
            mstore(add(out,416),sload(46)) mstore(add(out,448),sload(47))
            mstore(add(out,480),hx) mstore(add(out,512),hy)
            mstore(add(out,544),sload(hx)) mstore(add(out,576),sload(add(hx,1)))
            mstore(add(out,608),sload(add(hx,2))) mstore(add(out,640),sload(hy))
            mstore(add(out,672),tload(0))
        }
    }
    function fill() external returns(uint256[22] memory) {
        setA();n=type(uint248).max;mid=0x1234;
        xs.push(11);xs.push(type(uint256).max);ys.push(33);
        uint256[] storage left=xs;uint256[] storage right=xs;
        left[0]=right[0]+1;
        assembly ("memory-safe") {
            mstore(0,43) sstore(add(keccak256(0,32),2),77)
            tstore(0,0xdddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd7788)
        }
        return readAll();
    }
    function shrink() external returns(uint256[22] memory) {
        assembly ("memory-safe") { sstore(43,0) sstore(45,0) }
        return readAll();
    }
    function regrow() external returns(uint256[22] memory) {
        assembly ("memory-safe") { sstore(45,1) sstore(43,3) }
        return readAll();
    }
    function failAfterWrite() external {
        xs[0]=888;ys[0]=999;assembly ("memory-safe") { sstore(43,0) } revert("dynamic");
    }
    function outOfBounds() external view returns(uint256) { return xs[3]; }
    function staticProbe() external returns(bool) {
        (bool ok,)=address(this).staticcall(abi.encodeCall(this.shrink,()));return ok;
    }
}
