// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.34;
/// Guards H90 nonpayable address-local markers, tuples and environment copies.
contract AddressLocals {
 function zero() public pure { address a; address b; assert(a == b); }
 function sender() public view { address a = msg.sender; assert(a == msg.sender); }
 function repeated() public view { address a; address b = msg.sender; (a,a) = (b,a); assert(a == b); }
 function swap() public view { address a; address b = msg.sender; address z; (a,b) = (b,a); assert(a == msg.sender); assert(b == z); }
 function shadow() public view { address a = msg.sender; { address a; address z; assert(a == z); } assert(a == msg.sender); }
 function wrong() public view { address a = msg.sender; assert(a != msg.sender); }
 function parameter(address a) public pure { assert(a == a); }
 function payableLocal() public pure { address payable a; }
}
contract AddressStateRefusal { address a; function f() public view { assert(a == a); } }
