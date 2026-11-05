pragma solidity ^0.8.34; contract Identity { /// @custom:key box
function identity() public pure { uint[] memory m = new uint[](1); m[0] = 1; assert(m[0] == 1); } }
