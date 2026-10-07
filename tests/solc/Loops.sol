// SPDX-License-Identifier: GPL-3.0
pragma solidity ^0.8.0;

// Loops from solkey's TestSuite.sol past `ed7849d5b6`, for the front end's
// loop import (`Solidity/Examples/Tactics/LoopsImport.lean`), with Lean's own
// additions, which solkey does not read as they are:
// - the `/// @custom:key unwind k` clauses, Lean's bound on the unwinding,
//   which solkey's `KeyNatspec` rejects (solkey unwinds with no bound);
// - the functions marked "Lean's own", which solkey's TestSuite.sol does not
//   have.
contract Loops {
    uint[] values;
    uint total;

    function whileCountsUp() public pure {
        uint i = 0;
        /// @custom:key unwind 3
        while (i < 3) {
            i = i + 1;
        }
        assert(i == 3);
    }

    function forContinueStillUpdates() public pure {
        uint s = 0;
        /// @custom:key unwind 5
        for (uint i = 0; i < 5; i++) {
            if (i == 1) {
                continue;
            }
            s = s + i;
        }
        assert(s == 9);
    }

    function doWhileRunsBodyFirst() public pure {
        uint i = 7;
        /// @custom:key unwind 1
        do {
            i = i + 1;
        } while (i < 3);
        assert(i == 8);
    }

    function loopNestedReturn(uint k) internal pure returns (uint r) {
        for (uint i = 0; i < 3; i++) {
            for (uint j = 0; j < 3; j++) {
                if (i * 3 + j == k) {
                    return i * 10 + j;
                }
            }
        }
        r = 99;
    }

    // Lean's own: a `return` in the first of two loops that declare `i`.
    function returnBeforeSiblingLoop(uint k) internal pure returns (uint r) {
        for (uint i = 0; i < 3; i++) {
            if (i == k) {
                return i;
            }
        }
        for (uint i = 0; i < 2; i++) {
            r = r + i;
        }
    }

    /// @custom:key box
    function invariantCountsToBound(uint n) public pure {
        require(n >= 0);
        uint i = 0;
        /// @custom:key invariant i <= n
        while (i < n) {
            i = i + 1;
        }
        assert(i == n);
    }

    // Lean's own: an invariant over two `///` lines.
    /// @custom:key box
    function invariantTwoLines(uint n) public pure {
        require(n >= 0);
        uint s = 0;
        uint i = 0;
        /// @custom:key invariant i <= n
        ///     && s == i
        while (i < n) {
            s = s + 1;
            i = i + 1;
        }
        assert(s == n);
    }

    // Lean's own: the invariant at the head a `break` leaves from.
    /// @custom:key box
    function invariantBreak(uint n) public pure {
        uint i = 0;
        /// @custom:key invariant i <= 10
        while (i < 10) {
            if (i == n) break;
            i = i + 1;
        }
        assert(i <= 10);
    }

    function invariantVariantSkipsBreakIteration(uint n) public pure {
        uint i = 0;
        /// @custom:key invariant 0 <= i && i <= 10
        /// @custom:key decreases 10 - i
        while (i < 10) {
            if (i == n) break;
            i = i + 1;
        }
        assert(i <= 10);
    }
}
