pragma solidity ^0.8.34; contract Identity { 
function identity() public pure { int[][] memory m = new int[][](1); m[0] = new int[](1); int[] memory a = m[0]; a[0] = 1; assert(m[0][0] == 1); } }
