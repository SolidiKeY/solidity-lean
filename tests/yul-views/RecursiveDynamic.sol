pragma solidity =0.8.38;
contract RecursiveDynamic {
 struct I {uint16[] xs;int24[] ys;bytes3 tag;}
 struct M {uint16 guard;I inner;bool[] bs;}
 struct O {uint8 stamp;M mid;address who;}
 O box;uint256 marker;
 constructor(){assembly ("memory-safe"){
  sstore(0,0xa500000000000000000000000000000000000000000000000000000000000042)
  sstore(1,0xb600000000000000000000000000000000000000000000000000000000001234)
  sstore(4,0xc700000000000000000000000000000000000000000000000000000000010203)
  sstore(6,0xd800000000000000000000000000000000000000000000000000000000001234)
  mstore(0,2) let x:=keccak256(0,32)
  sstore(x,not(0)) sstore(add(x,1),0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccc8000004d)
  mstore(0,3) let y:=keccak256(0,32)
  sstore(y,not(0)) sstore(add(y,1),0xdddddddddddddddddddddddddddddddddddddddddddddddd80000000004d)
  mstore(0,5) sstore(keccak256(0,32),0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee02010101)
  sstore(8,999)
 }}
 function readAll() public view returns(uint256[] memory o){
  O storage a=box;O storage b=box;uint16[] storage x=a.mid.inner.xs;uint16[] storage z=b.mid.inner.xs;
  int24[] storage y=a.mid.inner.ys;bool[] storage bs=b.mid.bs;
  o=new uint256[](38);o[0]=x.length;o[1]=z.length;o[2]=y.length;o[3]=bs.length;
  o[4]=x.length>0?x[0]:0;o[5]=z.length>16?z[16]:0;o[6]=x.length>17?x[17]:0;
  o[7]=y.length>0?uint256(int256(y[0])):0;o[8]=y.length>9?uint256(int256(y[9])):0;
  o[9]=y.length>10?uint256(int256(y[10])):0;o[10]=y.length>11?uint256(int256(y[11])):0;
  o[11]=bs.length>0?(bs[0]?1:0):0;o[12]=bs.length>2?(bs[2]?1:0):0;o[13]=bs.length>3?(bs[3]?1:0):0;
  o[14]=b.stamp;o[15]=a.mid.guard;o[16]=uint24(b.mid.inner.tag);o[17]=uint160(a.who);o[18]=marker;
  assembly ("memory-safe") {let p:=add(o,32)
   mstore(add(p,608),sload(2)) mstore(add(p,640),sload(3)) mstore(add(p,672),sload(5))
   mstore(add(p,704),sload(0)) mstore(add(p,736),sload(1)) mstore(add(p,768),sload(4)) mstore(add(p,800),sload(6))
   mstore(0,2) let xh:=keccak256(0,32)
   mstore(add(p,832),sload(xh)) mstore(add(p,864),sload(add(xh,1))) mstore(add(p,1024),xh)
   mstore(0,3) let yh:=keccak256(0,32)
   mstore(add(p,896),sload(yh)) mstore(add(p,928),sload(add(yh,1))) mstore(add(p,1056),yh)
   mstore(0,5) let bh:=keccak256(0,32)
   mstore(add(p,960),sload(bh)) mstore(add(p,1088),bh) mstore(add(p,992),sload(8))
   mstore(add(p,1120),2) mstore(add(p,1152),3) mstore(add(p,1184),5)
  }
 }
 function fill() external returns(uint256[] memory){assembly ("memory-safe"){sstore(2,17) sstore(3,11) sstore(5,3)}return readAll();}
 function shrink() external returns(uint256[] memory){assembly ("memory-safe"){sstore(2,0) sstore(3,0)}return readAll();}
 function regrow() external returns(uint256[] memory){assembly ("memory-safe"){sstore(2,18) sstore(3,12)}return readAll();}
 function aliases() external returns(uint256[] memory){O storage a=box;O storage b=box;a.mid.inner.xs[16]=88;b.mid.inner.ys[11]=-1;b.mid.bs[0]=false;marker=222;return readAll();}
 function dirtyGrow() external returns(uint256[] memory){assembly ("memory-safe"){sstore(5,4)}return readAll();}
 function restore() external returns(uint256[] memory){assembly ("memory-safe"){sstore(5,3)}return readAll();}
 function failAfterWrite() external {assembly ("memory-safe"){sstore(2,1) sstore(3,1) sstore(5,0) sstore(7,123)}revert("recursive");}
 function outOfBounds() external view returns(uint16){return box.mid.inner.xs[18];}
 function staticProbe() external view returns(bool){(bool ok,)=address(this).staticcall(abi.encodeWithSignature("aliases()"));return ok;}
}
