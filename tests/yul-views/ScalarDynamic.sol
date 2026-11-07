pragma solidity =0.8.38;
contract ScalarDynamic {
 bool[] xs; uint256 marker; bytes3[] ys; address[] zs;
 constructor() { assembly ("memory-safe") {
  mstore(0,xs.slot) let x := keccak256(0,32)
  sstore(x,0x100010001000100010001000100010001000100010001000100010001000100) sstore(add(x,1),0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccc00020101)
  mstore(0,ys.slot) let y := keccak256(0,32)
  sstore(y,0xaabbfedcba778899445566112233000001800000ffffff000000abcdef010203) sstore(add(y,1),0xdddddddddddddddddddddddddddddddddddddddddddddddddddd112233ffffff)
  mstore(0,zs.slot) let z := keccak256(0,32)
  sstore(z,0xaaaaaaaaaaaaaaaaaaaaaaaa0000000000000000000000000000000000001234)
  sstore(add(z,1),0xbbbbbbbbbbbbbbbbbbbbbbbbffffffffffffffffffffffffffffffffffffffff)
  sstore(add(z,2),0xcccccccccccccccccccccccc1122334455667788990011223344556677889900)
  sstore(4,999)
 } }
 function readAll() public view returns(uint256[] memory o) {
  bool[] storage a=xs; bool[] storage b=xs; bytes3[] storage c=ys; address[] storage d=zs;
  o=new uint256[](36);
  o[0]=a.length;o[1]=b.length;o[2]=c.length;o[3]=d.length;
  o[4]=a.length>0?(a[0]?1:0):0;o[5]=b.length>31?(b[31]?1:0):0;
  o[6]=a.length>32?(a[32]?1:0):0;o[7]=b.length>33?(b[33]?1:0):0;
  o[8]=c.length>0?uint24(c[0]):0;o[9]=c.length>9?uint24(c[9]):0;
  o[10]=c.length>10?uint24(c[10]):0;o[11]=c.length>11?uint24(c[11]):0;
  o[12]=d.length>0?uint160(d[0]):0;o[13]=d.length>1?uint160(d[1]):0;o[14]=d.length>2?uint160(d[2]):0;
  o[15]=marker;o[33]=c.length>1?uint24(c[1]):0;
  o[34]=b.length>1?(b[1]?1:0):0;o[35]=b.length>34?(b[34]?1:0):0;
  assembly ("memory-safe") {
   let p:=add(o,32)
   mstore(add(p,512),sload(xs.slot)) mstore(add(p,544),sload(ys.slot)) mstore(add(p,576),sload(zs.slot))
   mstore(0,xs.slot) let x:=keccak256(0,32)
   mstore(add(p,608),sload(x)) mstore(add(p,640),sload(add(x,1)))
   mstore(0,ys.slot) let y:=keccak256(0,32)
   mstore(add(p,672),sload(y)) mstore(add(p,704),sload(add(y,1)))
   mstore(0,zs.slot) let z:=keccak256(0,32)
   mstore(add(p,736),sload(z)) mstore(add(p,768),sload(add(z,1))) mstore(add(p,800),sload(add(z,2)))
   mstore(add(p,832),sload(4)) mstore(add(p,864),x) mstore(add(p,896),y) mstore(add(p,928),z)
   mstore(add(p,960),a.slot) mstore(add(p,992),c.slot) mstore(add(p,1024),d.slot)
  }
 }
 function fill() external returns(uint256[] memory) { assembly ("memory-safe") {sstore(xs.slot,33) sstore(ys.slot,11) sstore(zs.slot,2)} return readAll(); }
 function shrinkOne() external returns(uint256[] memory) { assembly ("memory-safe") {sstore(xs.slot,1) sstore(ys.slot,1) sstore(zs.slot,1)} return readAll(); }
 function zero() external returns(uint256[] memory) { assembly ("memory-safe") {sstore(xs.slot,0) sstore(ys.slot,0) sstore(zs.slot,0)} return readAll(); }
 function regrow() external returns(uint256[] memory) { assembly ("memory-safe") {sstore(xs.slot,34) sstore(ys.slot,12) sstore(zs.slot,3)} return readAll(); }
 function readTyped() external view returns(bytes3,address,bool) { return(ys[0],zs[0],xs[0]); }
 function writeMembers() external returns(uint256[] memory) { xs[0]=true;xs[31]=false;xs[32]=false;xs[33]=true;ys[0]=0xa1b2c3;ys[9]=0x000001;ys[10]=0x010203;zs[0]=address(type(uint160).max);zs[1]=address(0);marker=555;return readAll(); }
 function dirtyGrow() external returns(uint256[] memory) {assembly ("memory-safe") {sstore(xs.slot,35)} return readAll();}
 function restore() external returns(uint256[] memory) {assembly ("memory-safe") {sstore(xs.slot,34)} return readAll();}
 function failAfterWrite() external {assembly ("memory-safe") {sstore(xs.slot,0) sstore(ys.slot,0) sstore(zs.slot,0) sstore(1,888)} revert("scalar");}
 function outOfBounds() external view returns(bool) {return xs[34];}
 function staticProbe() external view returns(bool) {(bool ok,)=address(this).staticcall(abi.encodeCall(this.zero,()));return ok;}
}
