// SPDX-License-Identifier: GPL-2.0-only
pragma solidity ^0.8.0;

/// The running contract of the storage-shape design (`docs/storage.md`, section 8c): a
/// fixed-size array has no length cell, so its length comes from the shaped empty storage in
/// the constructor and from `wellformed(storage)` in a function.
contract FixedLengths {
    uint[9] d1;
    uint[] d2;
    uint[3][] dyn;

    constructor() {
        d2 = d1;
        assert(d2.length == 9);
        delete d1;
        assert(d1.length == 9);
        dyn.push();
        assert(dyn[dyn.length - 1].length == 3);
        assert(dyn[0][0] == 0);
        assert(dyn[0][2] == 0);
    }

    function f() public {
        d2 = d1;
        assert(d2.length == 9);
    }

    function g() public {
        assert(d1.length == 9);
        delete d1;
        assert(d1.length == 9);
        dyn.push();
        assert(dyn[dyn.length - 1].length == 3);
    }

    function emptyPushReadsZero() public {
        uint n = d2.length;
        d2.push();
        assert(d2.length == n + 1);
        assert(d2[n] == 0);
    }

    function fixedCopyIsIndependent() public {
        d1[8] = 41;
        d2 = d1;
        d1[8] = 42;
        assert(d1.length == 9);
        assert(d2.length == 9);
        assert(d2[8] == 41);
        d2.push();
        assert(d2.length == 10);
        assert(d2[8] == 41);
        assert(d2[9] == 0);
    }

    function shorterCopyClearsTailBeforePush() public {
        d2 = d1;
        d2.push(99);
        d2 = d1;
        assert(d2.length == 9);
        d2.push();
        assert(d2[9] == 0);
    }

    function fixedElementMemoryCopyIsIndependent() public {
        uint n = dyn.length;
        dyn.push();
        dyn[n][2] = 51;
        uint[3] memory row = dyn[n];
        assert(row.length == 3);
        assert(row[2] == 51);
        row[2] = 52;
        assert(dyn[n][2] == 51);
        dyn[n] = row;
        row[2] = 53;
        assert(dyn[n].length == 3);
        assert(dyn[n][2] == 52);
    }

    function popPushResetsFixedElement() public {
        uint n = dyn.length;
        dyn.push();
        dyn[n][0] = 11;
        dyn[n][2] = 22;
        dyn.pop();
        assert(dyn.length == n);
        dyn.push();
        assert(dyn[n].length == 3);
        assert(dyn[n][0] == 0);
        assert(dyn[n][2] == 0);
    }

    function deleteFixedElementKeepsLength() public {
        uint n = dyn.length;
        dyn.push();
        dyn[n][1] = 17;
        delete dyn[n];
        assert(dyn.length == n + 1);
        assert(dyn[n].length == 3);
        assert(dyn[n][1] == 0);
    }

    function deleteDynamicThenPushFixedElement() public {
        dyn.push();
        dyn[0][2] = 23;
        delete dyn;
        assert(dyn.length == 0);
        dyn.push();
        assert(dyn.length == 1);
        assert(dyn[0].length == 3);
        assert(dyn[0][2] == 0);
    }

    function fixedElementStorageAlias() public {
        uint n = dyn.length;
        dyn.push();
        uint[3] storage row = dyn[n];
        assert(row.length == 3);
        row[2] = 31;
        assert(dyn[n][2] == 31);
        delete dyn[n];
        assert(row.length == 3);
        assert(row[2] == 0);
    }

    function emptyPushFixedElementReadsZero() public {
        uint n = dyn.length;
        dyn.push();
        assert(dyn.length == n + 1);
        assert(dyn[n].length == 3);
        assert(dyn[n][0] == 0);
        assert(dyn[n][2] == 0);
    }
}
