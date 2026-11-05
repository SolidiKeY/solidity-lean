pragma solidity ^0.8.34; contract Invalid { function test() public pure { int[] calldata m = new int[](1); } }
