// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.38;
contract JointMemory {
    struct Box { int8 tag; uint256[] data; bytes3 note; }
    function joint(bool reverse, bool regrow) public pure returns (uint256[34] memory out) {
        uint256[] memory a = new uint256[](3);
        a[0]=11; a[1]=22; a[2]=33;
        uint256[] memory c = new uint256[](2);
        c[0]=7; c[1]=9;
        Box memory x = Box(1,a,hex"112233");
        Box memory y = x;
        uint256[] memory d = c;
        bytes memory other = hex"aabbcc";
        uint256 freeBefore;
        assembly ("memory-safe") { freeBefore := mload(64) }
        out[24]=777; out[25]=888; out[32]=reverse?1:0; out[33]=regrow?1:0;
        if (regrow) {
            assembly ("memory-safe") { mstore(d,0) }
            out[24]=c.length; out[25]=d.length;
            assembly ("memory-safe") { mstore(c,2) }
        }
        if (reverse) {
            d[0]=type(uint256).max; c[1]=42;
            assembly ("memory-safe") { mstore(y,not(0)) mstore(add(y,32),c) mstore(add(y,64),shl(232,0xff00aa)) }
        } else {
            assembly ("memory-safe") { mstore(y,not(0)) mstore(add(y,32),c) mstore(add(y,64),shl(232,0xff00aa)) }
            d[0]=type(uint256).max; c[1]=42;
        }
        assembly ("memory-safe") {
            mstore(out,mload(x)) mstore(add(out,32),eq(mload(add(x,32)),c)) mstore(add(out,64),mload(add(x,64)))
            mstore(add(out,384),mload(add(a,96))) mstore(add(out,416),mload(add(c,32))) mstore(add(out,448),mload(add(c,64)))
            mstore(add(out,480),eq(mload(64),freeBefore)) mstore(add(out,512),mload(96))
            mstore(add(out,576),mload(add(other,32))) mstore(add(out,608),eq(x,y))
        }
        out[3]=c.length;out[4]=c[0];out[5]=c[1];out[6]=x.data[0];out[7]=y.data[1];
        out[8]=a.length;out[9]=a[0];out[10]=a[1];out[11]=a[2];out[17]=other.length;
        out[20]=uint8(x.note[0]);out[21]=uint256(int256(y.tag));out[22]=y.data.length;
        out[23]=d[0];out[26]=c.length;out[27]=d.length;out[28]=uint8(other[2]);
        out[29]=d[1];out[30]=x.data[1];out[31]=y.data[0];
    }
    function badAlias() public pure returns (uint256) {
        uint256[] memory a=new uint256[](2); Box memory x=Box(1,a,hex"112233");Box memory y=x;
        assembly ("memory-safe") { mstore(a,0) }
        return y.data[0];
    }
    function revertJoint() public pure { joint(true,true); revert(); }
}
