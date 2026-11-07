// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.38;
contract R { struct revert { uint x; } } contract C { function f() public { R.revert memory E; } }
