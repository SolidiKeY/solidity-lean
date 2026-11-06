pragma solidity ^0.8.34; contract Invalid { function test() public pure { bool[] memory m = new int[](1); } }
