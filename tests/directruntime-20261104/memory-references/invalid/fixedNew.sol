pragma solidity ^0.8.34; contract Invalid { function test() public pure { int[1] memory m = new int[1](1); } }
