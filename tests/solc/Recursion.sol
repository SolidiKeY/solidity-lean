// SPDX-License-Identifier: GPL-3.0
pragma solidity ^0.8.0;

// Recursive functions: a call of one is `Stmt.callRec`, proved by the
// callee's contract (its `requires`/`ensures`, `true`/`true` without one),
// the contract by induction over the frames (docs/kernel-port.md, "Recursion").
contract Recursion {
    uint a;

    // no spec: the contract `true`/`true`
    function countdown() public {
        if (a > 0) { a = a - 1; countdown(); } else { assert(a == 0); }
    }

    /// @custom:key requires n <= 1000
    /// @custom:key ensures \result == n * (n + 1) / 2
    function sum(uint n) public pure returns (uint) {
        if (n == 0) { return 0; }
        return n + sum(n - 1);
    }

    // open: the step is nonlinear (`n + (n - 1) * n / 2`), which the closer
    // (`omega`, `grind`) does not prove, so neither does the caller
    function sumThree() public pure { assert(sum(3) == 6); }

    // a sum the closer proves: `x + n`, one at a time
    /// @custom:key requires x <= 1000 && n <= 1000
    /// @custom:key ensures \result == x + n
    function sumTo(uint x, uint n) public pure returns (uint) {
        if (n == 0) { return x; }
        return sumTo(x, n - 1) + 1;
    }

    function sumToSix() public pure { assert(sumTo(3, 3) == 6); }

    /// @custom:key ensures \result == (n % 2 == 0)
    function even(uint n) public pure returns (bool) {
        if (n == 0) { return true; }
        return odd(n - 1);
    }

    /// @custom:key ensures \result == (n % 2 == 1)
    function odd(uint n) public pure returns (bool) {
        if (n == 0) { return false; }
        return even(n - 1);
    }

    function evenFour() public pure { assert(even(4) && !odd(4)); }

    // bounded: two recursive calls, unchecked; the contract fixes the base
    /// @custom:key requires n <= 20
    /// @custom:key ensures n <= 1 -> \result == n
    function fib(uint n) public pure returns (uint) {
        if (n <= 1) { return n; }
        unchecked { return fib(n - 1) + fib(n - 2); }
    }

    function fibOne() public pure { assert(fib(1) == 1); }

    // several returns
    /// @custom:key requires y > 0
    /// @custom:key ensures r < y && r <= x && q <= x
    function divmod(uint x, uint y) public pure returns (uint q, uint r) {
        if (x < y) { return (0, x); }
        (uint q1, uint r1) = divmod(x - y, y);
        return (q1 + 1, r1);
    }

    function divmodSeven() public pure {
        (uint q, uint r) = divmod(7, 2);
        assert(r < 2 && q <= 7);
    }

    function falsePost() public pure { assert(sumTo(3, 3) == 7); }

    // under the callback reading (O7): the value call's callee may call
    // back; the countdown after it does not (docs/kernel-port.md, "Recursion")
    function callThenCount(address to) public {
        (bool ok, ) = payable(to).call{value: 0}("");
        countdown();
    }

    // a recursion that calls back in every frame: its call by the contract
    // `true`/`true` over the callback runs, by induction over the frames
    function payDown(address to) public {
        if (a > 0) {
            a = a - 1;
            (bool ok, ) = payable(to).call{value: 0}("");
            payDown(to);
        }
    }
}
