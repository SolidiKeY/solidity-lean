pragma solidity ^0.8.34; contract Identity { /// @custom:key box
function identity() public pure { int[] memory m = new int[](1); int[] memory a = m; a[0] = -1; assert(m[0] == -1); } }
