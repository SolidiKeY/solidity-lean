// SPDX-License-Identifier: MIT
pragma solidity ^0.8.38;
contract C{error Err(uint code);function f() public{revert Err(1);}}
