// SPDX-License-Identifier: GPL-3.0
pragma solidity ^0.8.34;

// Ordinary deterministic scalar diamonds. No callback or tuple migration.
contract QuantifiedDiamond {
    mapping(uint => uint) values;
    function count() public pure returns (uint r) {
        /// @custom:key invariant r <= 3
        /// @custom:key invariant \forall uint q; q < r -> q < 3
        /// @custom:key decreases 3 - r
        while (r < 3) { r++; }
        assert(r == 3);
    }

    function forCount() public pure returns (uint r) {
        /// @custom:key invariant r <= 3
        /// @custom:key invariant \forall uint q; q < r -> q < 3
        /// @custom:key decreases 3 - r
        for (; r < 3; r++) { if (r == 1) continue; }
        assert(r == 3);
    }

    function nested() public pure returns (uint r) {
        /// @custom:key invariant r <= 3
        /// @custom:key invariant \forall uint q; \forall uint z; q < r -> q < 3 && z == z
        /// @custom:key decreases 3 - r
        while (r < 3) { r++; }
        assert(r == 3);
    }

    function undefinedVariant() public pure {
        uint r = 0;
        /// @custom:key invariant r <= 3
        /// @custom:key invariant \forall uint q; q < r -> q < 3
        /// @custom:key decreases 3 - r + 0 / (3 - r)
        while (r < 3) { r++; }
    }

    function fill() public {
        uint i = 0;
        /// @custom:key invariant i <= 3
        /// @custom:key invariant \forall uint q; q < i -> values[q] == 7
        /// @custom:key decreases 3 - i
        while (i < 3) { values[i] = 7; i++; }
    }

    function falsePost() public pure {
        uint r = 0;
        /// @custom:key invariant r <= 3
        /// @custom:key invariant \forall uint q; q < r -> q < 3
        /// @custom:key decreases 3 - r
        while (r < 3) { r++; }
        assert(r == 2);
    }

    function constantVariant() public pure {
        uint r = 0;
        /// @custom:key invariant r <= 3
        /// @custom:key invariant \forall uint q; q < r -> q < 3
        /// @custom:key decreases 0
        while (r < 3) { r++; }
    }

    function nonterminating() public pure {
        /// @custom:key invariant true
        /// @custom:key invariant \forall uint q; q == q
        /// @custom:key decreases 0
        while (true) {}
    }
}
