// SPDX-License-Identifier: GPL-2.0-only
pragma solidity ^0.8.0;

contract ArrayMatrixFD {
    uint[][2] a;
    uint[][2] b;

    function storageAliasSharesWrites() public {
        delete a;
        a[0].push();
        a[0].push();
        a[0][0] = 11;
        a[0][1] = 12;
        a[1].push();
        a[1].push();
        a[1][0] = 21;
        a[1][1] = 22;
        uint[][2] storage same = a;
        same[0][0] = 41;
        assert(a[0][0] == 41);
    }

    function storageAssignmentCopiesDeeply() public {
        delete a;
        a[0].push();
        a[0].push();
        a[0][0] = 11;
        a[0][1] = 12;
        a[1].push();
        a[1].push();
        a[1][0] = 21;
        a[1][1] = 22;
        delete b;
        b[0].push();
        b[0].push();
        b[0][0] = 71;
        b[0][1] = 72;
        b[1].push();
        b[1].push();
        b[1][0] = 81;
        b[1][1] = 82;
        b = a;
        a[0][0] = 99;
        assert(b[0][0] == 11);
        b[1][1] = 77;
        assert(a[1][1] == 22);
    }

    function storageToMemoryCopiesDeeply() public {
        delete a;
        a[0].push();
        a[0].push();
        a[0][0] = 11;
        a[0][1] = 12;
        a[1].push();
        a[1].push();
        a[1][0] = 21;
        a[1][1] = 22;
        uint[][2] memory m = a;
        a[0][0] = 99;
        assert(m[0][0] == 11);
        m[1][1] = 77;
        assert(a[1][1] == 22);
    }

    function memoryToStorageCopiesDeeply() public {
        uint[][2] memory m;
        m[0] = new uint[](2);
        m[0][0] = 11;
        m[0][1] = 12;
        m[1] = new uint[](2);
        m[1][0] = 21;
        m[1][1] = 22;
        delete b;
        b[0].push();
        b[0].push();
        b[0][0] = 71;
        b[0][1] = 72;
        b[1].push();
        b[1].push();
        b[1][0] = 81;
        b[1][1] = 82;
        b = m;
        m[0][0] = 99;
        assert(b[0][0] == 11);
        b[1][1] = 77;
        assert(m[1][1] == 22);
    }

    function memoryAssignmentSharesWrites() public pure {
        uint[][2] memory m;
        m[0] = new uint[](2);
        m[0][0] = 11;
        m[0][1] = 12;
        m[1] = new uint[](2);
        m[1][0] = 21;
        m[1][1] = 22;
        uint[][2] memory same = m;
        same[0][0] = 41;
        assert(m[0][0] == 41);
    }

    function storageRowAssignmentCopiesDeeply() public {
        delete a;
        a[0].push();
        a[0].push();
        a[0][0] = 11;
        a[0][1] = 12;
        a[1].push();
        a[1].push();
        a[1][0] = 21;
        a[1][1] = 22;
        a[1] = a[0];
        a[0][0] = 99;
        assert(a[1][0] == 11);
    }

    function memoryRowAliasBecomesIndependentStorageRows() public {
        uint[][2] memory m;
        m[0] = new uint[](2);
        m[0][0] = 11;
        m[0][1] = 12;
        m[1] = new uint[](2);
        m[1][0] = 21;
        m[1][1] = 22;
        m[1] = m[0];
        m[0][0] = 41;
        assert(m[1][0] == 41);
        delete b;
        b[0].push();
        b[0].push();
        b[0][0] = 71;
        b[0][1] = 72;
        b[1].push();
        b[1].push();
        b[1][0] = 81;
        b[1][1] = 82;
        b = m;
        b[0][0] = 99;
        assert(b[1][0] == 41);
        assert(m[0][0] == 41);
    }

    function deleteRowKeepsOuterLength() public {
        delete a;
        a[0].push();
        a[0].push();
        a[0][0] = 11;
        a[0][1] = 12;
        a[1].push();
        a[1].push();
        a[1][0] = 21;
        a[1][1] = 22;
        delete a[0];
        assert(a.length == 2);
        assert(a[0].length == 0);
        a[0].push();
        assert(a[0].length == 1);
        assert(a[0][0] == 0);
    }

    function deleteRootRestoresShapeAndDefaultValues() public {
        delete a;
        a[0].push();
        a[0].push();
        a[0][0] = 11;
        a[0][1] = 12;
        a[1].push();
        a[1].push();
        a[1][0] = 21;
        a[1][1] = 22;
        delete a;
        assert(a.length == 2);
        assert(a[0].length == 0);
        a[0].push();
        assert(a[0].length == 1);
        assert(a[0][0] == 0);
    }

    function popPushAtDepth2ResetsRemovedElement() public {
        delete a;
        a[0].push();
        a[0].push();
        a[0][0] = 11;
        a[0][1] = 12;
        a[1].push();
        a[1].push();
        a[1][0] = 21;
        a[1][1] = 22;
        a[0].pop();
        assert(a[0].length == 1);
        a[0].push();
        assert(a[0].length == 2);
        assert(a[0][1] == 0);
        assert(a[0][0] == 11);
    }
}
