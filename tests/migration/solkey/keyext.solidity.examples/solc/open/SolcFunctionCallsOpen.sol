// SPDX-License-Identifier: GPL-2.0-only
pragma solidity ^0.8.0;

contract SolcFunctionCallsOpen {
    uint a;

    function internalFunction(uint p, uint q, uint s) internal pure returns (uint r) {
        r = p * 100 + q * 10 + s * 1;
    }

    function publicFunction(uint p, uint q, uint s) internal pure returns (uint r) {
        r = p * 100 + q * 10 + s * 1;
    }

    function exp(uint base, uint exponent) internal pure returns (uint power) {
        if (exponent == 0)
            return 1;
        power = exp(base, exponent / 2);
        power *= power;
        if (exponent & 1 == 1)
            power *= base;
    }

    /// solc: semanticTests/freeFunctions/recursion.sol
    // open: no rule for the bitwise `&`
    function freeFunctionRecursionBitAnd() public pure {
        uint e23 = exp(2, 3);
        assert(e23 == 8);
    }

    function g(int p, int q) internal pure returns (int) {
        return p - q;
    }

    function h(int q, int p) internal pure returns (int) {
        return q - p;
    }

    /// solc: semanticTests/functionCall/conditional_with_arguments.sol
    // open: a call whose callee is a conditional expression is read as `false ? g : h(2, 1)` and gets stuck
    function conditionalWithArguments() public pure {
        int r = (false ? g : h)(2, 1);
        assert(r == 1);
    }

    function setA(uint v) internal {
        uint y;
        a = (y = v);
    }

    /// solc: smtCheckerTests/functions/functions_storage_var_1.sol
    // open: no rule for an assignment used as a value, `a = (y = v)`
    function functionsStorageVar1() public {
        setA(1);
        assert(a > 0);
    }

    /// solc: smtCheckerTests/functions/functions_storage_var_2.sol
    // open: no rule for an assignment used as a value, `a = (y = v)`
    function functionsStorageVar2() public {
        setA(1);
        setA(42);
        assert(a > 1);
    }

    /// solc: smtCheckerTests/functions/functions_recursive.sol
    // open: a uint state variable is not known to be non-negative, and the recursion unfolds without end
    function functionsRecursiveUnbounded() public {
        if (a > 0)
        {
            a = a - 1;
            functionsRecursiveUnbounded();
        }
        else
            assert(a == 0);
    }
}
