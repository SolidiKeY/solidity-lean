pragma solidity ^0.8.34; contract Identity { /// @custom:key box
function identity() public pure { int[1] memory m; int[1] memory a = m; a[0] = 1; assert(m[0] == 1); } }
