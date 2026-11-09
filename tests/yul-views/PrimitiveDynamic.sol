pragma solidity =0.8.38;
contract PrimitiveDynamic {
 int16[] ss;uint24[] us;uint256[] ws;bool[] bs;bytes3[] ys;address[] zs;uint256 marker;
 constructor(){assembly ("memory-safe"){
mstore(0,ss.slot) let h0:=keccak256(0,32)
sstore(add(h0,0),0xffffeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee00007fff8000ffff)
sstore(add(h0,1),0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccc8000004d)
mstore(0,us.slot) let h1:=keccak256(0,32)
sstore(add(h1,0),0xabcd11223300000b00000a000009000008000007000000800000ffffff000001)
sstore(add(h1,1),0xdddddddddddddddddddddddddddddddddddddddddddddddddddddddddd00004d)
mstore(0,ws.slot) let h2:=keccak256(0,32)
sstore(add(h2,0),0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
sstore(add(h2,1),0x4d)
mstore(0,bs.slot) let h3:=keccak256(0,32)
sstore(add(h3,0),0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee02010100)
mstore(0,ys.slot) let h4:=keccak256(0,32)
sstore(add(h4,0),0xf4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f400004daabbcc010203)
mstore(0,zs.slot) let h5:=keccak256(0,32)
sstore(add(h5,0),0xaaaaaaaaaaaaaaaaaaaaaaaa0000000000000000000000000000000000001234)
sstore(add(h5,1),0xbbbbbbbbbbbbbbbbbbbbbbbbffffffffffffffffffffffffffffffffffffffff)
sstore(7,999)}}
 function readAll() public view returns(uint256[] memory o){
  int16[] storage a=ss;bool[] storage b=bs;bool[] storage c=bs;
  o=new uint256[](52);
  o[0]=ss.length;o[1]=a.length;o[2]=us.length;o[3]=ws.length;o[4]=b.length;o[5]=c.length;o[6]=ys.length;o[7]=zs.length;
  o[8]=a.length>0?uint256(int256(a[0])):0;o[9]=a.length>16?uint256(int256(a[16])):0;o[10]=a.length>17?uint256(int256(a[17])):0;
  o[11]=us.length>0?us[0]:0;o[12]=us.length>9?us[9]:0;o[13]=us.length>10?us[10]:0;
  o[14]=ws.length>0?ws[0]:0;o[15]=ws.length>1?ws[1]:0;
  o[16]=b.length>0?(b[0]?1:0):0;o[17]=c.length>1?(c[1]?1:0):0;o[18]=b.length>2?(b[2]?1:0):0;o[19]=c.length>3?(c[3]?1:0):0;
  o[20]=ys.length>0?uint24(ys[0]):0;o[21]=ys.length>2?uint24(ys[2]):0;
  o[22]=zs.length>0?uint160(zs[0]):0;o[23]=zs.length>1?uint160(zs[1]):0;o[24]=marker;
  assembly ("memory-safe") {let p:=add(o,32)
mstore(add(p,800),sload(ss.slot))
mstore(add(p,832),sload(us.slot))
mstore(add(p,864),sload(ws.slot))
mstore(add(p,896),sload(bs.slot))
mstore(add(p,928),sload(ys.slot))
mstore(add(p,960),sload(zs.slot))
mstore(0,ss.slot) let h0:=keccak256(0,32)
mstore(add(p,992),sload(add(h0,0)))
mstore(add(p,1024),sload(add(h0,1)))
mstore(add(p,1344),h0)
mstore(0,us.slot) let h1:=keccak256(0,32)
mstore(add(p,1056),sload(add(h1,0)))
mstore(add(p,1088),sload(add(h1,1)))
mstore(add(p,1376),h1)
mstore(0,ws.slot) let h2:=keccak256(0,32)
mstore(add(p,1120),sload(add(h2,0)))
mstore(add(p,1152),sload(add(h2,1)))
mstore(add(p,1408),h2)
mstore(0,bs.slot) let h3:=keccak256(0,32)
mstore(add(p,1184),sload(add(h3,0)))
mstore(add(p,1440),h3)
mstore(0,ys.slot) let h4:=keccak256(0,32)
mstore(add(p,1216),sload(add(h4,0)))
mstore(add(p,1472),h4)
mstore(0,zs.slot) let h5:=keccak256(0,32)
mstore(add(p,1248),sload(add(h5,0)))
mstore(add(p,1280),sload(add(h5,1)))
mstore(add(p,1504),h5)
mstore(add(p,1312),sload(7)) mstore(add(p,1536),a.slot) mstore(add(p,1568),b.slot) mstore(add(p,1600),ys.slot) mstore(add(p,1632),zs.slot)
  }
 }
 function fill() external returns(uint256[] memory){assembly("memory-safe"){sstore(ss.slot,17) sstore(us.slot,11) sstore(ws.slot,2) sstore(bs.slot,3) sstore(ys.slot,3) sstore(zs.slot,2)}return readAll();}
 function writeBool() external returns(uint256[] memory){bs[0]=true;marker=111;return readAll();}
 function shrinkOne() external returns(uint256[] memory){assembly("memory-safe"){sstore(ss.slot,1) sstore(bs.slot,1)}return readAll();}
 function zero() external returns(uint256[] memory){assembly("memory-safe"){sstore(ss.slot,0) sstore(bs.slot,0)}return readAll();}
 function regrow() external returns(uint256[] memory){assembly("memory-safe"){sstore(ss.slot,18) sstore(bs.slot,3)}return readAll();}
 function writeSigned() external returns(uint256[] memory){ss[0]=type(int16).min;ss[17]=-1;marker=222;return readAll();}
 function writeMembers() external returns(uint256[] memory){us[0]=2;ws[0]=55;ys[0]=0xa1b2c3;zs[0]=address(type(uint160).max);marker=555;return readAll();}
 function dirtyGrow() external returns(uint256[] memory){assembly("memory-safe"){sstore(bs.slot,4)}return readAll();}
 function restore() external returns(uint256[] memory){assembly("memory-safe"){sstore(bs.slot,3)}return readAll();}
 function failAfterWrite() external {assembly("memory-safe"){sstore(ss.slot,0) sstore(bs.slot,0) sstore(6,888)}revert("combined");}
 function outOfBounds() external view returns(int16){return ss[18];}
 function staticProbe() external view returns(bool){(bool ok,)=address(this).staticcall(abi.encodeCall(this.zero,()));return ok;}
 function readTyped() external view returns(bytes3,address,bool,int16){return(ys[0],zs[0],bs[0],ss[0]);}
}
