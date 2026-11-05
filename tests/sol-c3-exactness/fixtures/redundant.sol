// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.38;
contract A {}
contract B is A {}
contract C is A, B {}
