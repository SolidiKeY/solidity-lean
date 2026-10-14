// SPDX-License-Identifier: GPL-3.0
pragma solidity ^0.8.0;

contract Runner {
    /// @custom:key box
    function passes(uint x) public pure {
        require(x == 7);
        assert(x == 7);
    }

    /// @custom:key box
    function staysOpen() public pure { assert(false); }

    /// @custom:key skip
    function ignored() public pure { assert(false); }

    function helper() internal pure {}

    function assemblyGap() public pure { assembly { mstore(0, 0) } }

    /// @custom:key ensures true
    function specified() public pure {}

    /// @custom:key ensures false
    function badSpec() public pure {}

    /// @custom:key box
    function boxRevert() public pure { revert(); }

    function diamondRevert() public pure { revert(); }

    /// @custom:key ensures msg.value == 0
    function payableSpec() public payable {}

    /// @custom:key invariant false
    function misplacedInvariant() public pure { assert(false); }
}

contract AnotherRunner {
    function passesToo() public pure { assert(true); }
}

/// @custom:key invariant value == 0
contract InvariantRunner {
    uint value;
    function breaksInvariant() public { value = 1; }
}

/// @custom:key invariant value == 0
contract ConstructorRunner {
    uint value;
    constructor() { value = 1; }
    function preservesInvariant() public view { assert(value == 0); }
}
