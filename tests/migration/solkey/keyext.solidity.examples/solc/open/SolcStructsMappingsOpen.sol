// SPDX-License-Identifier: GPL-2.0-only
pragma solidity ^0.8.0;

contract SolcStructsMappingsOpen {
    struct V { uint value; }
    struct PushZero { uint x; uint y; uint z; uint[3] a1; uint[] a2; }
    struct TA { uint y; uint[] a; }
    struct SA { uint x; TA t; uint[] a; TA[] ts; }

    uint pushB;
    PushZero[] pushZero;
    uint pushA;
    V[][] va;
    V[] vb;
    SA saStorage;
    SA[] saArray;

    /// solc: semanticTests/structs/copy_struct_array_from_storage.sol
    // open: temp[0] = va[0] (storage array copied into an element of a memory array of arrays) has no rule: symbolic execution stops on the statement
    /// @custom:key box
    function copyStructArraysIntoMemoryRows() public {
        require(va.length == 1);
        require(va[0].length == 3);
        require(vb.length == 4);
        vb[0].value = 4;
        vb[1].value = 5;
        vb[2].value = 6;
        vb[3].value = 7;
        V[][] memory temp = new V[][](2);
        temp[0] = va[0];
        temp[1] = vb;
        assert(temp.length == 2);
        assert(temp[0].length == 3);
        assert(temp[1].length == 4);
        assert(temp[1][0].value == 4);
        assert(temp[1][3].value == 7);
    }

    /// solc: smtCheckerTests/types/struct/struct_array_struct_array_storage_safe.sol
    // open: closes only with -m 300000 (~130 s); exceeds the suite budget of 50000 steps / 30 s
    /// @custom:key box
    function storageNestedStructArrays() public {
        require(saStorage.a.length == 0);
        require(saStorage.ts.length == 0);
        saStorage.x = 2;
        assert(saStorage.x == 2);
        saStorage.t.y = 3;
        assert(saStorage.t.y == 3);
        saStorage.a.push();
        saStorage.a.push();
        saStorage.a.push();
        saStorage.a[2] = 4;
        assert(saStorage.a[2] == 4);
        saStorage.ts.push();
        saStorage.ts.push();
        saStorage.ts.push();
        saStorage.ts.push();
        saStorage.ts.push();
        saStorage.ts[3].y = 5;
        assert(saStorage.ts[3].y == 5);
        saStorage.ts[4].a.push();
        saStorage.ts[4].a.push();
        saStorage.ts[4].a.push();
        saStorage.ts[4].a.push();
        saStorage.ts[4].a.push();
        saStorage.ts[4].a.push();
        saStorage.ts[4].a[5] = 6;
        assert(saStorage.ts[4].a[5] == 6);
    }

    /// solc: smtCheckerTests/types/struct/array_struct_array_struct_storage_safe.sol
    // open: closes only with -m 300000 (~340 s); exceeds the suite budget of 50000 steps / 30 s
    /// @custom:key box
    function storageArrayOfNestedStructArrays() public {
        require(saArray.length == 0);
        saArray.push();
        saArray.push();
        saArray.push();
        saArray[0].x = 2;
        assert(saArray[0].x == 2);
        saArray[1].t.y = 3;
        assert(saArray[1].t.y == 3);
        saArray[2].a.push();
        saArray[2].a.push();
        saArray[2].a.push();
        saArray[2].a[2] = 4;
        assert(saArray[2].a[2] == 4);
        saArray[0].ts.push();
        saArray[0].ts.push();
        saArray[0].ts.push();
        saArray[0].ts.push();
        saArray[0].ts.push();
        saArray[0].ts[3].y = 5;
        assert(saArray[0].ts[3].y == 5);
        saArray[1].ts.push();
        saArray[1].ts.push();
        saArray[1].ts.push();
        saArray[1].ts.push();
        saArray[1].ts.push();
        saArray[1].ts[4].a.push();
        saArray[1].ts[4].a.push();
        saArray[1].ts[4].a.push();
        saArray[1].ts[4].a.push();
        saArray[1].ts[4].a.push();
        saArray[1].ts[4].a.push();
        saArray[1].ts[4].a[5] = 6;
        assert(saArray[1].ts[4].a[5] == 6);
        saArray.pop();
        saArray.pop();
        saArray.pop();
    }
}
