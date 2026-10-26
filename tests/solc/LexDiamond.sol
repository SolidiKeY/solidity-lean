// SPDX-License-Identifier: GPL-2.0-only
pragma solidity ^0.8.34;

// No box tag: these are ordinary diamond obligations with the calculus's
// existing exhaustion policy, not strict SourceCertificate termination claims.
contract LexDiamond {
    uint n;
    uint m;

    function pairCountdown() public {
        /// @custom:key invariant true
        /// @custom:key decreases (n, 0)
        while (n > 0) { n--; }
        assert(n == 0);
    }

    function tripleCountdown() public {
        /// @custom:key invariant true
        /// @custom:key decreases (n, 0, 0)
        while (n > 0) { n--; }
        assert(n == 0);
    }

    function pairReset() public {
        /// @custom:key invariant true
        /// @custom:key decreases (n, m)
        while (n > 0 || m > 0) {
            if (m > 0) { m--; }
            else { n--; m = 2; }
        }
        assert(n == 0 && m == 0);
    }

    function tripleReset() public {
        /// @custom:key invariant true
        /// @custom:key decreases (n, m, 0)
        while (n > 0 || m > 0) {
            if (m > 0) { m--; }
            else { n--; m = 2; }
        }
        assert(n == 0 && m == 0);
    }

    // These bodies count down, but the supplied tuple does not decrease.
    function equalTuple() public {
        /// @custom:key invariant true
        /// @custom:key decreases (0, 0)
        while (n > 0) { n--; }
        assert(n == 0);
    }

    function increasingTuple() public pure {
        uint i = 0;
        /// @custom:key invariant i <= 2
        /// @custom:key decreases (i, 0)
        while (i < 2) { i++; }
        assert(i == 2);
    }

    // Every metric must be defined even when an earlier component decreases.
    function undefinedLater() public {
        /// @custom:key invariant true
        /// @custom:key decreases (n, 1 / 0)
        while (n > 0) { n--; }
    }

    // A false guard does not excuse an overflowing initial metric at n=max.
    function overflowMetric() public view {
        /// @custom:key invariant true
        /// @custom:key decreases (n + 1, 0)
        while (false) {}
    }

    function reverting() public view {
        /// @custom:key invariant true
        /// @custom:key decreases (n, 0)
        while (n > 0) { revert(); }
    }

    function breakDiamond() public view {
        /// @custom:key invariant true
        /// @custom:key decreases (n, 0)
        while (n > 0) { break; }
    }

    function quantifiedDiamond() public {
        /// @custom:key invariant true
        /// @custom:key invariant \forall uint q; q < n -> q < n
        /// @custom:key decreases (n, 0)
        while (n > 0) { n--; }
        assert(n == 0);
    }

    function noFrameDiamond() public {
        /// @custom:key invariant true
        /// @custom:key decreases (n, 0)
        while (n > 0) {
            uint[] memory temporary = new uint[](1);
            n--;
        }
        assert(n == 0);
    }

    function callbackDiamond(address target) public {
        /// @custom:key invariant true
        /// @custom:key decreases (0, 0)
        while (false) { LexDiamondTarget(target).g(); }
    }
}

contract LexDiamondTarget {
    uint n;
    function g() external { n++; }
}
