// SPDX-License-Identifier: GPL-2.0-only
pragma solidity ^0.8.0;

contract ArrayCubeDFD {
    uint[][2][] a;
    uint[][2][] b;

    function storageAliasSharesWrites() public {
        delete a;
        a.push();
        a.push();
        a[0][0].push();
        a[0][0].push();
        a[0][0][0] = 11;
        a[1][1].push();
        a[1][1].push();
        a[1][1][1] = 122;
        uint[][2][] storage same = a;
        same[0][0][0] = 41;
        assert(a[0][0][0] == 41);
    }

    function storageAssignmentCopiesDeeply() public {
        delete a;
        a.push();
        a[0][0].push(11);
        delete b;
        b = a;
        a[0][0][0] = 99;
        assert(b[0][0][0] == 11);
        b[0][0][0] = 77;
        assert(a[0][0][0] == 99);
    }

    function storageRowAssignmentCopiesDeeply() public {
        delete a;
        a.push();
        a.push();
        a[0][0].push();
        a[0][0].push();
        a[0][0][0] = 11;
        a[1][1].push();
        a[1][1].push();
        a[1][1][1] = 122;
        a[1] = a[0];
        a[0][0][0] = 99;
        assert(a[1][0][0] == 11);
    }

    function deleteRowKeepsOuterLength() public {
        delete a;
        a.push();
        a.push();
        a[0][0].push();
        a[0][0].push();
        a[0][0][0] = 11;
        a[1][1].push();
        a[1][1].push();
        a[1][1][1] = 122;
        delete a[0];
        assert(a.length == 2);
        assert(a[0].length == 2);
        assert(a[0][0].length == 0);
        a[0][0].push();
        assert(a[0][0].length == 1);
        assert(a[0][0][0] == 0);
    }

    function deleteRootRestoresShapeAndDefaultValues() public {
        delete a;
        a.push();
        a.push();
        a[0][0].push();
        a[0][0].push();
        a[0][0][0] = 11;
        a[1][1].push();
        a[1][1].push();
        a[1][1][1] = 122;
        delete a;
        assert(a.length == 0);
        a.push();
        assert(a.length == 1);
        assert(a[0].length == 2);
        assert(a[0][0].length == 0);
        a[0][0].push();
        assert(a[0][0].length == 1);
        assert(a[0][0][0] == 0);
    }

    function popPushAtDepth1ResetsRemovedElement() public {
        delete a;
        a.push();
        a.push();
        a[0][0].push();
        a[0][0].push();
        a[0][0][0] = 11;
        a[1][1].push();
        a[1][1].push();
        a[1][1][1] = 122;
        a.pop();
        assert(a.length == 1);
        a.push();
        assert(a.length == 2);
        assert(a[1].length == 2);
        assert(a[1][0].length == 0);
        a[1][0].push();
        assert(a[1][0].length == 1);
        assert(a[1][0][0] == 0);
        assert(a[0][0][0] == 11);
    }

    function pushArgumentAtDepth1CopiesDeeply() public {
        delete a;
        a.push();
        a.push();
        a[0][0].push();
        a[0][0].push();
        a[0][0][0] = 71;
        a[1][1].push();
        a[1][1].push();
        a[1][1][1] = 182;
        delete b;
        b.push();
        b.push();
        b[0][0].push();
        b[0][0].push();
        b[0][0][0] = 11;
        b[1][1].push();
        b[1][1].push();
        b[1][1][1] = 122;
        a.push(b[0]);
        b[0][0][0] = 99;
        assert(a[2][0][0] == 11);
    }

    function popPushAtDepth3ResetsRemovedElement() public {
        delete a;
        a.push();
        a.push();
        a[0][0].push();
        a[0][0].push();
        a[0][0][0] = 11;
        a[1][1].push();
        a[1][1].push();
        a[1][1][1] = 122;
        a[0][0].pop();
        assert(a[0][0].length == 1);
        a[0][0].push();
        assert(a[0][0].length == 2);
        assert(a[0][0][1] == 0);
        assert(a[0][0][0] == 11);
    }

    function pushReturnAliasSharesWrites() public {
        delete a;
        a.push();
        a.push();
        a[0][0].push();
        a[0][0].push();
        a[0][0][0] = 11;
        a[1][1].push();
        a[1][1].push();
        a[1][1][1] = 122;
        uint[][2] storage row = a.push();
        assert(row.length == 2);
        assert(row[0].length == 0);
        row[0].push();
        assert(row[0].length == 1);
        assert(row[0][0] == 0);
        row[0][0] = 41;
        assert(a.length == 3);
        assert(a[2][0][0] == 41);
    }
}
