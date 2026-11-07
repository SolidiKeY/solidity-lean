// SPDX-License-Identifier: GPL-3.0
pragma solidity >=0.8.0;
/// Guards H90 narrow-local regression: exact width, checked overflow,
/// unchecked wrapping, signed bounds and simultaneous tuple assignment.
contract NarrowLocalRuntime {
    function assignment() public pure { uint8 x = 3; x = 4; assert(x == 4); }
    function checkedOverflow() public pure { uint8 x = 255; x = x + 1; }
    function uncheckedWrap() public pure { uint8 x = 255; unchecked { x = x + 1; } assert(x == 0); }
    function signedOverflow() public pure { int8 x = 127; x = x + 1; }
    function signedWrap() public pure { int8 x = 127; unchecked { x = x + 1; } assert(x == -128); }
    function tupleSwap() public pure { (uint8 a, uint8 b) = (1, 2); (a, b) = (b, a); assert(a == 2 && b == 1); }
    function tupleRepeat() public pure { uint8 a = 1; uint8 b = 2; (a, a) = (b, a); assert(a == 2); }
    function tupleRepeatWrong() public pure { uint8 a = 1; uint8 b = 2; (a, a) = (b, a); assert(a == 1); }
    function narrowShadow() public pure { uint256 x = 300; { uint8 x = 1; x = 2; assert(x == 2); } x = x + 1; assert(x == 301); }
    function narrowParam(uint8 x) public pure returns(uint8) { return x; }
}
/// Guards the separate unchanged storage-width refusal boundary.
contract NarrowStateRefusal { uint8 x; }
