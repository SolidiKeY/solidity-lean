// SPDX-License-Identifier: MIT
pragma solidity ^0.8.34;
contract CompactScopes {
    uint public value;
    /// @custom:key ensures value == 3
    function scoped() public { value = 1; { uint local = 2; value = local; } value = 3; }
    /// @custom:key ensures value == 3
    function reusedName() public { { uint local = 2; value = local; } uint local = 3; value = local; }
    /// @custom:key ensures value == 2
    function falseScoped() public { value = 1; { uint local = 2; value = local; } value = 3; }
    /// @custom:key ensures value == 3
    function stateShadow() public { value = 1; { uint value = 2; } value = 3; }
}
contract CompactBuiltinShadow {
    function require(bool flag) internal pure {}
    /// @custom:key ensures \result == 1
    function wrong() public pure returns (uint result) { require(false); return 2; }
}
contract CompactAssertShadow {
    function assert(bool flag) internal pure {}
    /// @custom:key ensures \result == 1
    function wrong() public pure returns (uint result) { assert(false); return 2; }
}

contract CompactConstants {
    /// @custom:key ensures \result == 0
    function rationalConstant() public pure returns (uint result) { return 1 / 2 * 2; }
    /// @custom:key ensures \result == 0
    function implicitDefault() public pure returns (uint) { uint __solidity_direct_return_0 = 2; }
    /// @custom:key ensures \result == 2
    function falseImplicitDefault() public pure returns (uint) { uint __solidity_direct_return_0 = 2; }
    /// @custom:key ensures \result == 1
    function builtinAssert() public pure returns (uint result) { assert(true); return 1; }
    /// @custom:key ensures \result == 1
    function falseAfterRequire() public pure returns (uint result) { require(true); return 2; }
    /// @custom:key ensures \result == 1
    function reverting() public pure returns (uint result) { require(false); return 2; }
}
