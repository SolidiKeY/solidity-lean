pragma solidity ^0.8.34;

contract Preconditions {
    /// @custom:key requires amount > 10 && amount < 3
    /// @custom:key ensures false
    function impossible(uint amount) public pure { assert(false); }

    /// @custom:key requires amount > 0
    /// @custom:key ensures \result == amount
    function possible(uint amount) public pure returns (uint) { return amount; }

    /// @custom:key requires amount == 2
    /// @custom:key ensures false
    function badPost(uint amount) public pure { assert(false); }

    function plain() public pure { assert(true); }

    // The parameter pools have far more combinations than the search budget.
    /// @custom:key requires true
    /// @custom:key ensures true
    function wide(uint a, uint b, uint c, uint d, uint e, uint f,
                  uint g, uint h, uint i, uint j, uint k, uint l) public pure {}
}
