// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.38;
import {B} from "B.sol"; contract D is B { function f(bool) internal pure returns (uint) { return 2; } function g() external pure returns (uint) { return f(1); } }
