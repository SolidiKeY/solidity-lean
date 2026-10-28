pragma solidity ^0.8.0;
type Ticket is uint8;
type Switch is bool;
type Account is address;
contract NativePositive {
 enum Choice { A, B, C }
 uint counter;
 function identifiers() public pure returns(uint) { uint $x=7; {uint $x=10;$x++;}return $x; }
 function wrappers() public pure returns(uint) {Ticket t=Ticket.wrap(255);Switch s=Switch.wrap(true);Account a=Account.wrap(address(7));assert(Switch.unwrap(s));assert(Account.unwrap(a)==address(7));return Ticket.unwrap(t);}
 function bounds() public pure returns(uint) {assert(type(int8).min==-128);assert(uint(type(Choice).max)==2);return type(uint8).max;}
 function falseBounds() public pure {assert(type(uint8).max==254);}
 function checkedHelper(uint8 x) internal pure returns(uint8){return x+1;}
 function uncheckedCaller() public pure returns(uint){unchecked{return checkedHelper(255);}}
 function setCounter() public {counter=3;}
 function writeFail() public {counter=9;assert(false);}
 function readCounter() public view returns(uint){return counter;}
}
