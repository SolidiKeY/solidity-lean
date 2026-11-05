pragma solidity ^0.8.34; contract Identity { /// @custom:key box
function identity() public pure { int[] memory m = new int[](1); m[1] = 1; assert(false); } }
