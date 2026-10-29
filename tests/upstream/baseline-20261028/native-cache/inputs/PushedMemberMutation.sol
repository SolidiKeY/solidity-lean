pragma solidity ^0.8.0;
contract PushedMemberMutation {
 struct S {uint x;} S[] a; uint counter;
 function receiver() internal returns(S[] storage){counter++;return a;}
 function compound() public returns(uint){receiver().push().x+=7;return counter*100+a[a.length-1].x;}
 function constantStore() public returns(uint){receiver().push().x=7;return counter*100+a[a.length-1].x;}
}
