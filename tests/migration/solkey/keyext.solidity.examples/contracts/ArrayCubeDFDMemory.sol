// SPDX-License-Identifier: GPL-2.0-only
pragma solidity ^0.8.0;

contract ArrayCubeDFDMemory {
    uint[][2][] a;
    uint[][2][] b;

    function storageToMemoryCopiesDeeply() public {
        delete a;
        a.push();
        a.push();
        a[0][0].push();
        a[0][0].push();
        a[0][0][0] = 11;
        a[1][1].push();
        a[1][1].push();
        a[1][1][1] = 122;
        uint[][2][] memory m = a;
        a[0][0][0] = 99;
        assert(m[0][0][0] == 11);
        m[1][1][1] = 77;
        assert(a[1][1][1] == 122);
    }

    function memoryToStorageCopiesDeeply() public {
        uint[][2][] memory m = new uint[][2][](2);
        m[0][0] = new uint[](2);
        m[0][0][0] = 11;
        m[1][1] = new uint[](2);
        m[1][1][1] = 122;
        delete b;
        b.push();
        b.push();
        b[0][0].push();
        b[0][0].push();
        b[0][0][0] = 71;
        b[1][1].push();
        b[1][1].push();
        b[1][1][1] = 182;
        b = m;
        m[0][0][0] = 99;
        assert(b[0][0][0] == 11);
        b[1][1][1] = 77;
        assert(m[1][1][1] == 122);
    }

    function memoryAssignmentSharesWrites() public pure {
        uint[][2][] memory m = new uint[][2][](2);
        m[0][0] = new uint[](2);
        m[0][0][0] = 11;
        m[1][1] = new uint[](2);
        m[1][1][1] = 122;
        uint[][2][] memory same = m;
        same[0][0][0] = 41;
        assert(m[0][0][0] == 41);
    }

    function memoryRowAliasBecomesIndependentStorageRows() public {
        uint[][2][] memory m = new uint[][2][](2);
        m[0][0] = new uint[](1);
        m[0][0][0] = 11;
        m[1] = m[0];
        m[0][0][0] = 41;
        assert(m[1][0][0] == 41);
        delete b;
        b = m;
        b[0][0][0] = 99;
        assert(b[1][0][0] == 41);
        assert(m[0][0][0] == 41);
    }
}
