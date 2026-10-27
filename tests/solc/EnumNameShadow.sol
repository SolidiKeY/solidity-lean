pragma solidity ^0.8.0;
library EnumNameLibrary { enum E { A, B } }
contract EnumNameShadow {
    uint enumType4;
    function ident(uint x) internal pure returns (uint) { return x + 1; }
    function invoke(function(uint) internal pure returns (uint) enumType4, uint x)
        internal pure returns (uint) { return enumType4(x); }
    function f() public pure returns (uint) { return invoke(ident, 0); }
    function invokeCast(function(uint) internal pure returns (uint) enumType4, uint x)
        internal pure returns (uint) { return uint(EnumNameLibrary.E(x)); }
    function cast() public pure returns (uint) { return invokeCast(ident, 0); }
    function checkCast() public pure { assert(cast() == 0); }
    function check() public pure { assert(f() == 1); }
}
