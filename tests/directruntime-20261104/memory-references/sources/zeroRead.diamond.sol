pragma solidity ^0.8.34; contract Identity { 
function identity() public pure { int[] memory m = new int[](0); assert(m[0] == 0); } }
