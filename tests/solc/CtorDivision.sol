// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;
// A quotient of an unsigned parameter: `sol_close` reads solc's `x / k` at a
// nonnegative dividend as `div` (solkey's `sdiv_axiom`), in a constructor and
// in a function alike.
contract CtorDivision {
    uint got;
    constructor(uint x) { got = x / 2; assert(got == x / 2); }
    function half(uint x) public pure { uint y = x / 2; assert(y == x / 2 && y <= x); }
}
contract CtorDivisionLiteral {
    uint got;
    constructor() { uint seven = 7; got = seven / 2; assert(got == 3); }
}
contract CtorModulo {
    uint got;
    constructor(uint x) { got = x % 3; assert(got == x % 3); }
}
contract CtorDivisionFalse {
    uint got;
    constructor(uint x) { got = x / 2; assert(got == x / 3); }
}
