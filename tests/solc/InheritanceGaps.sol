// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;
contract PrivateRoot { uint private x; }
contract NameGap is PrivateRoot { uint private x; function f() public pure { assert(true); } }
