// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.34;
/// Guards primitive-return admission, early-exit and expression-failure regressions.
contract PrimitiveReturnRuntime {
 function value() public pure returns (uint) { return 7; }
 function namedDefault() public pure returns (uint result) { assert(result == 0); }
 function tuple() public pure returns (uint, bool) { return (1, true); }
 function early() public pure returns (uint) { if (true) { return 3; } assert(false); return 4; }
 function loopExit() public pure returns (uint) { while (true) { return 3; } }
 function shadow() public pure returns (uint result) { { uint result = 9; assert(result == 9); } assert(result == 0); }
 function bad() public pure returns (uint) { assert(false); return 1; }
 function division() public pure returns (uint) { uint zero = 0; return 1 / zero; }
}
