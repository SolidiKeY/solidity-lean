pragma solidity ^0.8.38;
contract EnumErrorControls {
    enum Flag { A, B }
    struct Box { Flag flag; }
    error EnumArray(Flag[] value);
    error EnumNested(Flag[][] value);
    error EnumBox(Box value);
    function direct() public pure { Flag[] memory a = new Flag[](0); revert EnumArray(a); }
    function nested() public pure { Flag[][] memory a = new Flag[][](0); revert EnumNested({value:a}); }
    function boxed() public pure { revert EnumBox(Box(Flag.A)); }
}
