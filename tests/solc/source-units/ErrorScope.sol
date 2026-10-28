pragma solidity ^0.8.0;
contract Other { error Bad(uint8 x); function wrong() external pure { revert Bad(1); } }
contract ErrorScope {
    error Bad(uint256 x);
    function callOther(Other other) public { other.wrong(); }
    function value() public pure { revert Bad(7); }
    function requireValue() public pure { require(false, Bad(7)); }
}
