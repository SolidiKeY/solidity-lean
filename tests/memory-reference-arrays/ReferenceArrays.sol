// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;
contract ReferenceArrays {
    function dynamicAliases() external pure returns (uint) {
        uint[][] memory a = new uint[][](2);
        a[0] = new uint[](1); a[0][0] = 7; a[1] = a[0];
        uint[] memory y = new uint[](1); y[0] = 9;
        uint[] memory x = y;
        x = a[0]; a[0] = y; x[0] = 11; a[0][0] = 13;
        require(a[1][0] == 11);
        return x[0] * 1000 + a[0][0];
    }
    function fixedAliases() external pure returns (uint) {
        uint[][2] memory a;
        a[0] = new uint[](1); a[0][0] = 7; a[1] = a[0];
        uint[] memory y = new uint[](1); y[0] = 9;
        uint[] memory x = y;
        x = a[0]; a[0] = y; x[0] = 11; a[0][0] = 13;
        require(a[1][0] == 11);
        return x[0] * 1000 + a[0][0];
    }
    function fixedChildAliases() external pure returns (uint) {
        uint[1][2] memory a;
        a[0][0] = 7; a[1] = a[0];
        uint[1] memory y; y[0] = 9;
        uint[1] memory x = y;
        x = a[0]; a[0] = y; x[0] = 11; a[0][0] = 13;
        require(a[1][0] == 11);
        return x[0] * 1000 + a[0][0];
    }
    function distinctFixedDefaults() external pure returns (uint) {
        uint[1][2] memory a; a[0][0] = 3; return a[1][0];
    }
    function parentBounds() external pure returns (uint) {
        uint[][] memory a = new uint[][](2); uint i = 2; return a[i].length;
    }
    function fixedParentBounds() external pure returns (uint) {
        uint[][2] memory a; uint i = 2; return a[i].length;
    }
    function childBounds() external pure returns (uint) {
        uint[][] memory a = new uint[][](2); return a[0][0];
    }
    function fixedChildBounds() external pure returns (uint) {
        uint[1][2] memory a; uint i = 1; return a[0][i];
    }
}
