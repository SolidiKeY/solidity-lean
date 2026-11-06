// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;
contract ControlTupleObligations {
    function goodDo() external pure { uint x;
        /// @custom:key unwind 1
        do { x = x + 1; } while (false); assert(x == 1); }
    function badDo() external pure { uint x;
        /// @custom:key unwind 1
        do { x = x + 1; } while (false); assert(x == 0); }
    function zeroWhile() external pure { uint x;
        /// @custom:key unwind 1
        while (false) { x = x + 1; } assert(x == 0); }
    function continues() external pure { uint x;
        /// @custom:key unwind 2
        do { x = x + 1; continue; } while (x < 2); assert(x == 2); }
    function breaks() external pure { uint x;
        /// @custom:key unwind 1
        do { x = x + 1; break; } while (true); assert(x == 1); }
    function early() external pure {
        /// @custom:key unwind 1
        do { return; } while (true); assert(false); }
    function tupleSwap() external pure { uint a = 1; uint b = 2;
        (a, b) = (b, a); assert(a == 2); assert(b == 1); }
    function repeat() external pure { uint a; (a, a) = (1, 2); assert(a == 1); }
    function hole() external pure { uint a; (, a) = (9, 5); assert(a == 5); }
    function reverting() external pure { require(false); assert(false); }
    function returnGuard() external pure returns (uint) { return 1; }
}
