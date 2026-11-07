// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.38;
error E(); contract C { function f() public { revert E(); } }
