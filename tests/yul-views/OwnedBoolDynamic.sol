pragma solidity =0.8.38;
contract OwnedBoolDynamic {
 bool[] xs; uint16 small; uint256 marker;
 constructor(){assembly("memory-safe"){
  mstore(0,xs.slot) let h:=keccak256(0,32)
  sstore(h,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee02010100)
  sstore(add(h,1),or(shl(248,0xab),0x024d))
  sstore(1,or(shl(248,0xcd),0x1234)) sstore(2,777)
 }}
 function snap() public view returns(uint256[] memory o){
  bool[] storage a=xs;bool[] storage b=xs;
  uint n=a.length;uint count;for(uint i;i<n;i++){if(a[i])count++;}
  o=new uint256[](12);o[0]=n;o[1]=a.length;o[2]=b.length;o[3]=count;
  o[4]=n>32?(a[32]?1:0):0;o[5]=n>33?(b[33]?1:0):0;
  assembly("memory-safe"){mstore(0,xs.slot)let h:=keccak256(0,32)mstore(add(o,224),sload(h))mstore(add(o,256),sload(add(h,1)))mstore(add(o,320),sload(1))}
  o[8]=small;o[10]=marker;o[11]=999;
 }
 function grow() external returns(uint256[] memory){assembly("memory-safe"){sstore(xs.slot,34)}return snap();}
 function zero() external returns(uint256[] memory){assembly("memory-safe"){sstore(xs.slot,0)}return snap();}
 function regrow() external returns(uint256[] memory){assembly("memory-safe"){sstore(xs.slot,34)}return snap();}
 function payload() external returns(uint256[] memory){assembly("memory-safe"){
  mstore(0,xs.slot)let h:=keccak256(0,32)
  sstore(h,or(and(sload(h),not(shl(24,255))),shl(24,3)))
  sstore(add(h,1),or(and(sload(add(h,1)),not(shl(8,255))),shl(8,255)))
 }return snap();}
 function childFail() external{assembly("memory-safe"){mstore(0,xs.slot)let h:=keccak256(0,32)sstore(h,0)sstore(add(h,1),0)sstore(xs.slot,0)}revert("dynamic bool");}
 function outerFail() external{this.zero();revert("outer");}
 function staticProbe() external view returns(bool,uint256){(bool ok,bytes memory reason)=address(this).staticcall(abi.encodeCall(this.zero,()));return(ok,reason.length);}
 function bounds() external view returns(bool){return xs[34];}
}
