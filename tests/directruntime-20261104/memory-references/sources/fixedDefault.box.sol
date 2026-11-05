pragma solidity ^0.8.34; contract Identity { /// @custom:key box
function identity() public pure { int[1] memory m; assert(m[0] == 0); } }
