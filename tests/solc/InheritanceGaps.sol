// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;
contract BaseCtor { uint n; constructor(uint x) { n = x; } }
contract CtorGap is BaseCtor(7) { function f() public pure { assert(true); } }
/// @custom:key invariant n == 1
contract BaseSpec { uint n; }
contract SpecGap is BaseSpec { function f() public pure { assert(true); } }
contract PrivateRoot { uint private x; }
contract NameGap is PrivateRoot { uint private x; function f() public pure { assert(true); } }
