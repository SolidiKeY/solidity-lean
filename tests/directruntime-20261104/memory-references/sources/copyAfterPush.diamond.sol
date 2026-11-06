pragma solidity ^0.8.34; contract Identity { int[] stored;
function identity() public  { stored.push(0); uint i = stored.length - 1; int[] memory m = stored; m[i] = 1; assert(stored[i] == 0); } }
