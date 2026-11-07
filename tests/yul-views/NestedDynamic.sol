pragma solidity =0.8.38;
contract NestedDynamic {
 struct S {uint16 guard;uint16[] xs;int24[] ys;bytes3 tag;address who;}
 S box;bool[] top;uint256 marker;
 constructor(){assembly ("memory-safe"){
  sstore(0,0xa500000000000000000000000000000000000000000000000000000000001234)
  sstore(3,0xaa00000000000000000000000000000000000000000000000000001234010203)
  mstore(0,1) let x:=keccak256(0,32)
  sstore(x,not(0)) sstore(add(x,1),0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccc8000004d)
  mstore(0,2) let y:=keccak256(0,32)
  sstore(y,not(0)) sstore(add(y,1),0xdddddddddddddddddddddddddddddddddddddddddddddddd80000000004d)
  mstore(0,4) sstore(keccak256(0,32),0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee02010101)
  sstore(6,999)
 }}
 function readAll() public view returns(uint256[] memory o){
  S storage a=box;S storage b=box;uint16[] storage x=a.xs;uint16[] storage z=b.xs;
  o=new uint256[](31);o[0]=x.length;o[1]=z.length;o[2]=a.ys.length;o[3]=top.length;
  o[4]=x.length>0?x[0]:0;o[5]=z.length>16?z[16]:0;o[6]=x.length>17?x[17]:0;
  o[7]=b.ys.length>0?uint256(int256(b.ys[0])):0;o[8]=a.ys.length>9?uint256(int256(a.ys[9])):0;
  o[9]=b.ys.length>10?uint256(int256(b.ys[10])):0;o[10]=top.length>0?(top[0]?1:0):0;
  o[11]=top.length>2?(top[2]?1:0):0;o[12]=top.length>3?(top[3]?1:0):0;
  o[13]=b.guard;o[14]=uint24(a.tag);o[15]=uint160(b.who);o[16]=marker;
  assembly ("memory-safe") {let p:=add(o,32)
   mstore(add(p,544),sload(1)) mstore(add(p,576),sload(2)) mstore(add(p,608),sload(4))
   mstore(add(p,640),sload(0)) mstore(add(p,672),sload(3))
   mstore(0,1) let xh:=keccak256(0,32)
   mstore(add(p,704),sload(xh)) mstore(add(p,736),sload(add(xh,1))) mstore(add(p,896),xh)
   mstore(0,2) let yh:=keccak256(0,32)
   mstore(add(p,768),sload(yh)) mstore(add(p,800),sload(add(yh,1))) mstore(add(p,928),yh)
   mstore(0,4) let bh:=keccak256(0,32)
   mstore(add(p,832),sload(bh)) mstore(add(p,960),bh) mstore(add(p,864),sload(6))
  }
 }
 function fill() external returns(uint256[] memory){assembly ("memory-safe"){sstore(1,17) sstore(2,11) sstore(4,3)}return readAll();}
 function shrink() external returns(uint256[] memory){assembly ("memory-safe"){sstore(1,0) sstore(2,0)}return readAll();}
 function regrow() external returns(uint256[] memory){assembly ("memory-safe"){sstore(1,18) sstore(2,12)}return readAll();}
 function aliases() external returns(uint256[] memory){S storage a=box;S storage b=box;a.xs[16]=88;b.ys[11]=-1;top[0]=false;marker=222;return readAll();}
 function dirtyGrow() external returns(uint256[] memory){assembly ("memory-safe"){sstore(4,4)}return readAll();}
 function restore() external returns(uint256[] memory){assembly ("memory-safe"){sstore(4,3)}return readAll();}
 function failAfterWrite() external {assembly ("memory-safe"){sstore(1,1) sstore(2,1) sstore(4,0) sstore(5,123)}revert("nested");}
 function outOfBounds() external view returns(uint16){return box.xs[18];}
 function staticProbe() external view returns(bool){(bool ok,)=address(this).staticcall(abi.encodeWithSignature("aliases()"));return ok;}
}
