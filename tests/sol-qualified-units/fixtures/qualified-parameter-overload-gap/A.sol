// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.38;
import * as L from "B.sol"; import * as R from "C.sol"; contract D is L.B { function f(R.T) internal pure returns (uint) { return 2; } function g() external pure returns (uint) { return f(L.T.a); } }
