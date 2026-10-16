// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

uint constant GLOBAL_LIMIT = 3;

/// @custom:key invariant COUNT == 2
contract SpecConstants {
    uint constant LIMIT = (1 + 2) * 1 ether;
    uint constant COUNT = 2;
    /// @custom:key ensures LIMIT == 3000000000000000000 && GLOBAL_LIMIT == 3
    function exactUnits() public pure {}
    /// @custom:key ensures LIMIT == 4
    function falseConstant() public pure {}
    /// @custom:key box
    function boundedLoop() public pure {
        uint i = 0;
        /// @custom:key invariant i <= COUNT
        while (i < 2) { i++; }
        assert(i == 2);
    }
    /// @custom:key ensures LIMIT == 3000000000000000000
    function parameterShadow(uint LIMIT) public pure {}
    /// @custom:key ensures \forall uint COUNT; COUNT == 2
    function quantifiedShadow() public pure {}
}

contract OtherConstants {
    uint constant LIMIT = 5;
    /// @custom:key ensures LIMIT == 5
    function ownScope() public pure {}
}

contract PrivateConstants {
    uint private constant SECRET = 7;
    uint internal constant SHARED = 2;
    /// @custom:key ensures SECRET == 7
    function definingScope() public pure {}
}

contract InheritedConstants is PrivateConstants {
    /// @custom:key ensures SHARED == 2
    function inheritedVisible() public pure {}
    /// @custom:key ensures SECRET == 7
    function privateIsHidden() public pure {}
    function callDefiningScope() public pure { definingScope(); }
}

contract ConstantTypes {
    uint constant K = 1;
    /// @custom:key ensures K + x == x + 1
    function signedMix(int x) public pure {}
}

library LibraryConstants { uint constant LIB_ONLY = 4; }

contract ConstantIsolation {
    /// @custom:key ensures LIMIT == 5
    function invisibleConstant() public pure {}
    /// @custom:key ensures LIB_ONLY == 4
    function invisibleLibraryConstant() public pure {}
}
