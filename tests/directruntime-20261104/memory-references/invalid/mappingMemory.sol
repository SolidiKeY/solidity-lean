pragma solidity ^0.8.34; contract Invalid { function test() public pure { mapping(uint => int) memory m; } }
