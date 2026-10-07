// SPDX-License-Identifier: GPL-3.0
pragma solidity ^0.8.0;

// Loops as solkey writes them (its TestSuite.sol past `ed7849d5b6`), for the
// front end's loop import (`Solidity/Examples/Tactics/LoopsImport.lean`).
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
        do {
            i = i + 1;
        } while (i < 3);
        assert(i == 8);
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

    function invariantVariant(uint n) public pure {
        require(n <= 1000);
        uint i = 0;
        /// @custom:key invariant 0 <= i && i <= n
        /// @custom:key decreases n - i
        while (i < n) {
            i = i + 1;
        }
        assert(i == n);
    }
}
