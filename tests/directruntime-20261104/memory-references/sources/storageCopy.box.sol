pragma solidity ^0.8.34; contract Identity { int[] stored;/// @custom:key box
function identity() public view { require(stored.length == 1); require(stored[0] == 0); int[] memory m = stored; m[0] = 1; assert(stored[0] == 0); } }
