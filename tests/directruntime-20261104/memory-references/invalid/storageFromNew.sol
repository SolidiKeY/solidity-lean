pragma solidity ^0.8.34; contract Invalid { function test() public pure { int[] storage m = new int[](1); } }
