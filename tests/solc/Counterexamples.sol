pragma solidity ^0.8.34;

contract Counterexamples {
    /// @custom:key requires x == 2
    /// @custom:key ensures false
    function falsePost(uint x) public pure {}

    /// @custom:key requires true
    /// @custom:key ensures false
    function falsePost(bool x) public pure {}

    /// @custom:key requires true
    /// @custom:key ensures \result == x
    function correct(uint x) public pure returns (uint) { return x; }

    /// @custom:key requires x > 10 && x < 3
    /// @custom:key ensures false
    function vacuous(uint x) public pure {}

    /// @custom:key requires amount == 115792089237316195423570985008687907853269984665640564039457584007913129639935
    /// @custom:key ensures false
    function large(uint amount) public pure {}

    /// @custom:key requires true
    /// @custom:key ensures false
    function names(address from, uint value, uint value_, int $x, bool) public pure {}

    function plain() public pure { assert(false); }

    /// @custom:key requires true
    /// @custom:key ensures false
    function recursive(uint x) public pure returns (uint) {
        if (x == 0) return 0;
        return recursive(x - 1);
    }
}
