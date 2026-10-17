// SPDX-License-Identifier: GPL-2.0-only
pragma solidity ^0.8.0;

contract SolcStructArrays {
    struct TA { uint y; uint[] a; }
    struct SA { uint x; TA t; uint[] a; TA[] ts; }

    SA saStorage;
    SA[] saArray;

    /// solc: smtCheckerTests/types/struct/struct_array_struct_array_storage_safe.sol
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
