// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.38;
type revert is uint256; contract C { function f() public { revert x; } }
