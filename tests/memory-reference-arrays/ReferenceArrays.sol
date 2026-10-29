// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;
contract ReferenceArrays {
    struct Holder { uint[] items; }
    struct Box { uint value; bool flag; }
    function structDefaultAliases() external pure returns (uint) {
        uint n = 2; Box[] memory a = new Box[](n);
        Box memory x = a[0]; a[0] = a[1]; x.value = 11; a[0].value = 13;
        require(!x.flag && !a[0].flag);
        return x.value * 1000 + a[0].value;
    }
    function fixedDefaultAliases() external pure returns (uint) {
        uint[1][2] memory a; uint[1] memory x = a[0]; a[0] = a[1];
        x[0] = 11; a[0][0] = 13; return x[0] * 1000 + a[0][0];
    }
    function dynamicFixedDefaultAliases() external pure returns (uint) {
        uint n = 2; uint[1][] memory a = new uint[1][](n);
        uint[1] memory x = a[0]; a[0] = a[1]; x[0] = 11; a[0][0] = 13;
        return x[0] * 1000 + a[0][0];
    }
    function nestedFixedDefaultAliases() external pure returns (uint) {
        uint[1][2][2] memory a; uint[1][2] memory x = a[0]; a[0] = a[1];
        x[0][0] = 11; a[0][0][0] = 13; return x[0][0] * 1000 + a[0][0][0];
    }
    function referenceArrayRebind() external pure returns (uint) {
        uint n = 2; uint[1][] memory a = new uint[1][](n);
        uint[1] memory x = a[0]; a[0] = a[1]; x[0] = 11; a[0][0] = 13;
        a = new uint[1][](n); x[0] = 17;
        return x[0] * 1000 + a[0][0];
    }
    function fixedDynamicDefaultAliases() external pure returns (uint) {
        uint[][2] memory a; uint[] memory x = a[0]; uint[] memory right = new uint[](1);
        a[0] = right; right[0] = 13; return x.length * 1000 + a[0][0];
    }
    function structDefaultBounds() external pure returns (uint) {
        uint n = 2; Box[] memory a = new Box[](n); return a[n].value;
    }
    function dynamicFixedDefaultBounds() external pure returns (uint) {
        uint n = 2; uint[1][] memory a = new uint[1][](n); return a[0][n - 1];
    }
    function nestedFixedDefaultBounds() external pure returns (uint) {
        uint n = 2; uint[1][2][2] memory a; return a[0][n][0];
    }
    function fixedDynamicDefaultBounds() external pure returns (uint) {
        uint[][2] memory a; return a[0][0];
    }
    function dynamicAliases() external pure returns (uint) {
        uint[][] memory a = new uint[][](2);
        a[0] = new uint[](1); a[0][0] = 7; a[1] = a[0];
        uint[] memory y = new uint[](1); y[0] = 9;
        uint[] memory x = y;
        x = a[0]; a[0] = y; x[0] = 11; a[0][0] = 13;
        require(a[1][0] == 11);
        return x[0] * 1000 + a[0][0];
    }
    function reallocAliases() external pure returns (uint) {
        uint[][] memory empty; require(empty.length == 0);
        uint n = 2;
        uint[][] memory a = new uint[][](n);
        uint[] memory left = new uint[](1); left[0] = 7;
        uint[] memory right = new uint[](1); right[0] = 9;
        a[0] = left; a[1] = left;
        uint[] memory x = right;
        x = a[0]; a[0] = right; x[0] = 11; a[0][0] = 13;
        a = new uint[][](n);
        require(a[0].length == 0 && a[1].length == 0);
        return x[0] * 1000 + right[0];
    }
    function zeroParentBounds() external pure returns (uint) {
        uint n = 0; uint[][] memory a = new uint[][](n); return a[0].length;
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
    function structInputAliases() external pure returns (uint) {
        uint[] memory left = new uint[](1); left[0] = 7;
        uint[] memory right = new uint[](1); right[0] = 9;
        Holder memory l = Holder(left); Holder memory r = Holder(right);
        Holder[2] memory a; a[0] = l; a[1] = l;
        Holder memory x = r;
        x = a[0]; a[0] = r; x.items[0] = 11; a[0].items[0] = 13;
        require(a[1].items[0] == 11);
        return x.items[0] * 1000 + a[0].items[0];
    }
    function structParentBounds() external pure returns (uint) {
        Holder[2] memory a; uint i = 2; return a[i].items.length;
    }
    function emptyFixedChildren() external pure returns (uint) {
        uint[1][] memory a = new uint[1][](0);
        a = new uint[1][](0);
        return a.length;
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
