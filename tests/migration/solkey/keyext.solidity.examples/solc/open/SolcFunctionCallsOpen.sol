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

    function setA(uint v) internal {
        uint y;
        a = (y = v);
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
