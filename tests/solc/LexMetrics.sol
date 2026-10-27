pragma solidity ^0.8.34;

contract LexMetrics {
    /// @custom:key box
    function resetInner() public pure {
        uint outer = 2;
        uint inner = 2;
        /// @custom:key invariant outer <= 2 && inner <= 2
        /// @custom:key decreases (outer, inner)
        while (outer > 0 || inner > 0) {
            if (inner > 0) inner--;
            else { outer--; inner = 2; }
        }
        assert(outer == 0 && inner == 0);
    }

    /// @custom:key box
    function triple() public pure {
        uint x = 1;
        /// @custom:key invariant x <= 1
        /// @custom:key decreases (x, 1, 2)
        while (x > 0) { x--; }
        assert(x == 0);
    }

    /// @custom:key box
    function forScope() public pure {
        /// @custom:key invariant i <= 2
        /// @custom:key decreases (i, 0)
        for (uint i = 2; i > 0; i--) {}
    }

    /// @custom:key box
    function doWhileLoop() public pure {
        uint x = 1;
        /// @custom:key invariant x <= 1
        /// @custom:key decreases (x, 0)
        do { x = 0; } while (x > 0);
        assert(x == 0);
    }

    /// @custom:key box
    function breakLoop() public pure {
        uint x = 2;
        /// @custom:key invariant x <= 2
        /// @custom:key decreases (x, 0)
        while (x > 0) {
            if (x == 1) break;
            x--;
        }
        assert(x <= 2);
    }

    /// @custom:key box
    function continueLoop() public pure {
        /// @custom:key invariant i <= 2
        /// @custom:key decreases (2 - i, 0)
        for (uint i = 0; i < 2; i++) {
            if (i == 0) continue;
            assert(i < 2);
        }
    }

    /// @custom:key box
    function renamed(uint from) public pure {
        /// @custom:key invariant true
        /// @custom:key decreases (from, 0)
        while (from > 0) { from--; }
    }

    /// @custom:key box
    function nested() public pure {
        uint outer = 1;
        /// @custom:key invariant outer <= 1
        /// @custom:key decreases (outer, 0)
        while (outer > 0) {
            uint inner = 1;
            /// @custom:key invariant inner <= 1
            /// @custom:key decreases (outer, inner)
            while (inner > 0) { inner--; }
            outer--;
        }
        assert(outer == 0);
    }

    /// @custom:key box
    function shadowed() public pure {
        uint x = 1;
        {
            uint x = 2;
            /// @custom:key invariant x <= 2
            /// @custom:key decreases (x, 0)
            while (x > 0) { x--; }
            assert(x == 0);
        }
        assert(x == 1);
    }

    /// @custom:key box
    function callback(address target) public {
        /// @custom:key invariant true
        /// @custom:key decreases (0, 0)
        while (false) { LexTarget(target).g(); }
    }

    /// @custom:key box
    function earlyReturn() public pure returns (uint) {
        uint n = 1;
        /// @custom:key invariant n <= 1
        /// @custom:key decreases (n, 0)
        while (n > 0) { return n; }
        return 0;
    }

    function diamondCountdown() public pure {
        uint n = 1;
        /// @custom:key invariant n <= 1
        /// @custom:key decreases (n, 0)
        while (n > 0) { n--; }
    }
}

contract LexTarget {
    uint n;
    function g() external { n++; }
}

contract InvalidLexMetrics {
    function schemaEscape() public pure {
        /// @custom:key invariant true
        /// @custom:key decreases ‹LoopMetrics.nil›
        while (false) {}
    }

    function wrongType(bool flag) public pure {
        /// @custom:key invariant true
        /// @custom:key decreases (flag, 0)
        while (false) {}
    }

    function badSecond(bool flag) public pure {
        /// @custom:key invariant true
        /// @custom:key decreases (0, flag)
        while (false) {}
    }

    function badThird(bool flag) public pure {
        /// @custom:key invariant true
        /// @custom:key decreases (0, 0, flag)
        while (false) {}
    }

    function unknown() public pure {
        /// @custom:key invariant true
        /// @custom:key decreases (missing, 0)
        while (false) {}
    }

    function nestedTuple(uint x) public pure {
        /// @custom:key invariant true
        /// @custom:key decreases (x, (x, 0))
        while (false) {}
    }

    function effect(uint x) public pure {
        /// @custom:key invariant true
        /// @custom:key decreases (x++, 0)
        while (false) {}
    }

    function cast(int x) public pure {
        /// @custom:key invariant true
        /// @custom:key decreases (uint(x), 0)
        while (false) {}
    }

    function empty() public pure {
        /// @custom:key invariant true
        /// @custom:key decreases ()
        while (false) {}
    }

    function trailing(uint x) public pure {
        /// @custom:key invariant true
        /// @custom:key decreases (x,)
        while (false) {}
    }

    function duplicate(uint x) public pure {
        /// @custom:key invariant true
        /// @custom:key decreases (x, 0)
        /// @custom:key decreases x
        while (false) {}
    }

    function noInvariant(uint x) public pure {
        /// @custom:key decreases (x, 0)
        while (false) {}
    }

    function conflicting(uint x) public pure {
        /// @custom:key invariant true
        /// @custom:key decreases (x, 0)
        /// @custom:key unwind 1
        while (false) {}
    }
}
