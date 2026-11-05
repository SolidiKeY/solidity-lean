pragma solidity ^0.8.34; contract Identity { /// @custom:key box
function identity() public pure { bool[] memory m = new bool[](1); assert(!m[0]); } }
