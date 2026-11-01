// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.38;
contract OwnedInventory {
    struct Box { bool flag; uint256[] words; bytes3 tag; }
    function inventory(uint256 n, bool reverse, bool shrink) public pure returns (uint256[] memory out) {
        uint256[] memory shared = new uint256[](2); shared[0]=7;shared[1]=9;
        uint256[][] memory cells = new uint256[][](n);
        Box[] memory boxes = new Box[](n);
        for(uint256 i=0;i<n;i++) {
            if(i%2==0) cells[i]=shared;
            else {cells[i]=new uint256[](2);cells[i][0]=i;cells[i][1]=i+1;}
            boxes[i]=Box(true,cells[i],hex"112233");
        }
        bytes memory other=hex"aabbcc";
        out=new uint256[](8+7*n);
        uint256 freeBefore; assembly ("memory-safe") {freeBefore:=mload(64)}
        out[0]=n;out[1]=reverse?1:0;out[2]=shrink?1:0;out[3]=shrink?0:777;
        for(uint256 step=0;step<n;step++) {
            uint256 i=reverse?n-1-step:step;
            Box memory b=boxes[i];Box memory aliasBox=b;
            aliasBox.words=shared;
            uint256[] memory a=b.words;uint256[] memory aliasArray=a;
            if(shrink) {assembly ("memory-safe") {mstore(aliasArray,0)} out[3]+=a.length;assembly ("memory-safe") {mstore(a,2)}}
            a[0]=100+i;aliasArray[1]=type(uint256).max;
            assembly ("memory-safe") {mstore(aliasBox,0) mstore(add(aliasBox,64),shl(232,0xff00aa))}
        }
        assembly ("memory-safe") {mstore(add(out,160),eq(mload(64),freeBefore)) mstore(add(out,192),mload(96)) mstore(add(out,224),mload(add(other,32)))}
        out[7]=shared[0];
        for(uint256 i=0;i<n;i++) {
            Box memory b=boxes[i];uint256 j=8+7*i;
            uint256 rawTag;uint256 rawFlag;uint256 pointerEq;
            assembly ("memory-safe") {rawTag:=mload(add(b,64)) rawFlag:=mload(b) pointerEq:=eq(mload(add(b,32)),shared)}
            out[j]=rawTag;out[j+1]=rawFlag;out[j+2]=pointerEq;
            out[j+3]=b.words[0];out[j+4]=b.words[1];out[j+5]=cells[i][0];out[j+6]=b.words.length;
        }
    }
    function lateFailure() public pure returns(uint256) {
        inventory(3,true,true);uint256[] memory empty=new uint256[](0);return empty[0];
    }
    function revertInventory() public pure {inventory(3,false,true);revert();}
}
