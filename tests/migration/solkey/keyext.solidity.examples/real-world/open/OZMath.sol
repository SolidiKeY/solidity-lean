// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// Source: https://github.com/OpenZeppelin/openzeppelin-contracts/blob/v5.0.0/contracts/utils/math/Math.sol
// Changes: as in ../OZMath.sol; these are the functions whose proof does not close.
contract OZMath {
    // open: program / is sdiv and spec / is div; automation proves neither sdiv(a, b) = div(a, b) nor sdiv(a, b) >= 0 for a >= 0, b >= 1
    /// @custom:key requires a >= 0 && b >= 0
    /// @custom:key ensures success <-> b != 0
    /// @custom:key ensures success -> r == a / b
    /// @custom:key ensures !success -> r == 0
    function tryDiv(uint256 a, uint256 b) public pure returns (bool success, uint256 r) {
        unchecked {
            if (b == 0) return (false, 0);
            return (true, a / b);
        }
    }

    // open: program % is smod and spec % is mod; automation does not prove 0 <= smod(a, b) < b for a >= 0, b >= 1
    /// @custom:key requires a >= 0 && b >= 0
    /// @custom:key ensures success <-> b != 0
    /// @custom:key ensures success -> r == a % b
    /// @custom:key ensures !success -> r == 0
    function tryMod(uint256 a, uint256 b) public pure returns (bool success, uint256 r) {
        unchecked {
            if (b == 0) return (false, 0);
            return (true, a % b);
        }
    }

    // open: & and ^ have no rule (no bitwise LDT), so the body is stuck on its program text
    /// @custom:key requires a >= 0 && b >= 0
    /// @custom:key ensures r == (a + b) / 2
    function average(uint256 a, uint256 b) public pure returns (uint256 r) {
        return (a & b) + (a ^ b) / 2;
    }

    // open: automation derives no bound on sdiv(a - 1, b), not even sdiv(a - 1, b) >= 0
    /// @custom:key requires a >= 0 && b > 0
    /// @custom:key ensures a == 0 -> r == 0
    /// @custom:key ensures a > 0 -> r * b >= a && (r - 1) * b < a
    function ceilDiv(uint256 a, uint256 b) public pure returns (uint256 r) {
        if (b == 0) {
            return a / b;
        }
        return a == 0 ? 0 : (a - 1) / b + 1;
    }
}
