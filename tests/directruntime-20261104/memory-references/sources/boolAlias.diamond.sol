pragma solidity ^0.8.34; contract Identity { 
function identity() public pure { bool[] memory m = new bool[](1); bool[] memory a = m; a[0] = true; assert(m[0]); } }
