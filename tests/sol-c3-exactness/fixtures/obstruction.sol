// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.38;
contract A {}
contract B {}
contract X is A, B {}
contract Y is B, A {}
contract Z is X, Y {}
contract W is Z {}
