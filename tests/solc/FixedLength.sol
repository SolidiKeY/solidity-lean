// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

// A fixed-length array copied into a dynamic one: the copy reads its source
// at the destination's shape (`Op1.fixedCopy`), which the LaTeX export prints
// (`Solidity/Examples/Tactics/Latex.lean`).
contract C {
    uint[9] d1;
    uint[] d2;
    uint[3][] dyn;

    function f() public returns (uint x) {
        d2 = d1;
        x = d2.length;
        assert(x == 9);
    }
}
