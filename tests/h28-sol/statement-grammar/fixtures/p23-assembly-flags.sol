// SPDX-License-Identifier: MIT
pragma solidity ^0.8.38;
contract C{function f() public{assembly "evmasm" ("memory-safe"){let x:=1 pop(x)}}}
