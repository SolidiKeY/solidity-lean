// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.38;
contract A {}
contract B is A {}
contract C is A {}
contract D is B, C {}
contract E is B, C {}
contract F is D, E {}
