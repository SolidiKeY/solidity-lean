pragma solidity ^0.8.34; contract Identity { int[] stored; /// @custom:key box
function identity() public  { int[] storage a = stored; a[0] = 1; assert(stored[0] == 1); } }
