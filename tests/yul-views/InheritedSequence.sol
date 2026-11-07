// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.38;
contract DiamondA {
    uint8 private a;
    function readA() internal view returns (uint8) { return a; }
    function setA(uint8 x) internal { a=x; }
}
contract DiamondB is DiamondA { uint248 b; }
contract DiamondC is DiamondA {
    struct Inner { bool flag; uint16 small; }
    bool c;
    Inner[2] items;
}
contract InheritedSequence is DiamondB, DiamondC {
    uint248 e;
    uint16 f;
    uint256 marker;
    uint16 transient temp;
    constructor() {
        marker=55;
        assembly ("memory-safe") {
            sstore(1,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00)
            sstore(2,0xbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb000000)
            sstore(3,0xbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb000000)
            sstore(4,0xee00000000000000000000000000000000000000000000000000000000000000)
            sstore(5,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc0000)
            sstore(7,999)
        }
    }
    function readAll() public view returns(uint256[20] memory out) {
        assembly ("memory-safe") {
            mstore(out,sload(0)) mstore(add(out,32),sload(1))
            mstore(add(out,64),sload(2)) mstore(add(out,96),sload(3))
            mstore(add(out,128),sload(4)) mstore(add(out,160),sload(5))
            mstore(add(out,192),sload(6)) mstore(add(out,224),sload(7))
            mstore(add(out,608),tload(0))
        }
        out[8]=readA();out[9]=b;out[10]=c?1:0;
        Inner[2] storage left=items; Inner[2] storage right=items;
        out[11]=left[0].flag?1:0;out[12]=left[0].small;
        out[13]=right[1].flag?1:0;out[14]=right[1].small;
        out[15]=e;out[16]=f;out[17]=marker;out[18]=temp;
    }
    function writeForward() external returns(uint256[20] memory) { write(false);return readAll(); }
    function writeReverse() external returns(uint256[20] memory) { write(true);return readAll(); }
    function write(bool reverse) internal {
        if(reverse) {
            f=0x4567;e=0x123456;
            for(uint z=0;z<2;z++){uint n=1-z;Inner storage p=items[n];p.small=uint16(0x3333+n);p.flag=false;}
            c=false;b=type(uint248).max-1;setA(18);
            assembly ("memory-safe") { tstore(0,0xdddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd9999) }
        } else {
            setA(17);b=type(uint248).max;c=true;
            for(uint n=0;n<2;n++){Inner storage p=items[n];p.flag=true;p.small=uint16(0x2222+n);}
            e=0x9876;f=0x3456;
            assembly ("memory-safe") { tstore(0,0xdddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd7788) }
        }
    }
    function failAfterWrite() external { write(false);revert("inherited"); }
}
