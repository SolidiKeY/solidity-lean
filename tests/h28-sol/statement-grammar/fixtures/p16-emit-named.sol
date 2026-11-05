// SPDX-License-Identifier: MIT
pragma solidity ^0.8.38;
contract C{event E(uint code);function f() public{emit E({code:1});}}
