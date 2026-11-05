// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.38;
import * as N from "B.sol"; import * as N from "C.sol"; contract D is N.Base {} contract Use { D.S value; }
