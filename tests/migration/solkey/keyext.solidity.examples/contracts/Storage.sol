// SPDX-License-Identifier: GPL-2.0-only
pragma solidity ^0.8.0;

contract Storage {
    struct Strct {
        uint i;
    }

    uint i;
    uint j;
    uint res;
    Strct a;
    Strct d;
    uint[] array;

    int[] arrayStorage;
    int simpleExprStorage = 1;
    int leftStorage = 4;
    int rightStorage = 2;
    int varStorage;
    bool varStorageBool;
    bool simpleExprBoolStorage = true;

    /// @custom:key ensures \result == 8
    function m() public returns (uint r) {
        a.i = 8;
        r = a.i;
    }

    /// @custom:key ensures \result > 0
    function a1() public returns (uint r) {
        i = 0;
        a.i = 3;
        d.i = 3;
        uint x = a.i;
        uint y = d.i;
        i = x + y;
        r = i;
    }

    /// @custom:key requires arrayStorage.length > 0
    /// @custom:key ensures \result > 2
    function d1() public returns (int r) {
        require(0 < arrayStorage.length);
        simpleExprStorage = 1;
        arrayStorage[0] = 7;
        simpleExprStorage = arrayStorage[0];
        r = simpleExprStorage;
    }

    /// @custom:key ensures \result > 0
    function f() public returns (int r) {
        leftStorage = 4;
        rightStorage = 2;
        int l = leftStorage;
        int rt = rightStorage;
        varStorage = l + rt;
        r = varStorage;
    }

    /// @custom:key ensures \result == 7
    function h() public returns (int r) {
        bool sb = simpleExprBoolStorage;
        varStorageBool = !sb;
        r = 7;
    }
}
