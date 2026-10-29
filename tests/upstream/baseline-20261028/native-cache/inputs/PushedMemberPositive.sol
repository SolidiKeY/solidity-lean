pragma solidity ^0.8.0;
contract PushedMemberPositive {
 struct S {uint x;} S[] a;
 function positive() public returns(uint){a.push();a[0].x++;return a[0].x;}
}
