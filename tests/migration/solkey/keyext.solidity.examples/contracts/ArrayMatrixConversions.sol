// SPDX-License-Identifier: GPL-2.0-only
pragma solidity ^0.8.0;

contract ArrayMatrixConversions {
    uint[2][2] ff;
    uint[2][] df;
    uint[][2] fd;
    uint[][] dd;
    uint[][1] shortRows;
    uint[2][] dfTarget;
    uint[][] ddTarget;

    function fixedRowsToDynamicOuter() public {
        delete ff;
        ff[0][0] = 11;
        ff[0][1] = 12;
        ff[1][0] = 21;
        ff[1][1] = 22;
        delete df;
        df.push();
        df.push();
        df[0][0] = 71;
        df[0][1] = 72;
        df[1][0] = 81;
        df[1][1] = 82;
        df = ff;
        ff[0][0] = 99;
        assert(df.length == 2);
        assert(df[0].length == 2);
        assert(df[0][0] == 11);
        assert(df[1][1] == 22);
    }

    function fixedRowsToDynamicInner() public {
        delete ff;
        ff[0][0] = 11;
        ff[0][1] = 12;
        ff[1][0] = 21;
        ff[1][1] = 22;
        delete fd;
        fd[0].push();
        fd[0].push();
        fd[0][0] = 71;
        fd[0][1] = 72;
        fd[1].push();
        fd[1].push();
        fd[1][0] = 81;
        fd[1][1] = 82;
        fd = ff;
        ff[0][0] = 99;
        assert(fd.length == 2);
        assert(fd[0].length == 2);
        assert(fd[0][0] == 11);
        fd[0].push();
        assert(fd[0].length == 3);
        assert(fd[0][2] == 0);
    }

    function fixedRowsToDynamicBoth() public {
        delete ff;
        ff[0][0] = 11;
        ff[0][1] = 12;
        ff[1][0] = 21;
        ff[1][1] = 22;
        delete dd;
        dd.push();
        dd.push();
        dd[0].push();
        dd[0].push();
        dd[0][0] = 71;
        dd[0][1] = 72;
        dd[1].push();
        dd[1].push();
        dd[1][0] = 81;
        dd[1][1] = 82;
        dd = ff;
        assert(dd.length == 2);
        assert(dd[0].length == 2);
        assert(dd[0][0] == 11);
        dd[0].pop();
        dd[0].push();
        assert(dd[0][1] == 0);
        assert(ff[0][1] == 12);
    }

    function dynamicRowsToDynamicOuter() public {
        delete fd;
        fd[0].push(11);
        fd[1].push(22);
        delete dd;
        dd.push();
        dd[0].push(71);
        dd = fd;
        fd[0][0] = 99;
        assert(dd.length == 2);
        assert(dd[0].length == 1);
        assert(dd[0][0] == 11);
        assert(dd[1].length == 1);
        assert(dd[1][0] == 22);
    }

    function shorterFixedOuterClearsDynamicRow() public {
        delete shortRows;
        shortRows[0].push(11);
        shortRows[0].push(12);
        delete fd;
        fd[0].push();
        fd[0].push();
        fd[0][0] = 71;
        fd[0][1] = 72;
        fd[1].push();
        fd[1].push();
        fd[1][0] = 81;
        fd[1][1] = 82;
        fd = shortRows;
        assert(fd.length == 2);
        assert(fd[0].length == 2);
        assert(fd[0][0] == 11);
        assert(fd[1].length == 0);
        fd[1].push();
        assert(fd[1][0] == 0);
    }

    function dynamicFixedShrinkClearsReusedRow() public {
        delete df;
        df.push();
        df[0][0] = 11;
        delete dfTarget;
        dfTarget.push();
        dfTarget.push();
        dfTarget[1][0] = 99;
        dfTarget = df;
        assert(dfTarget.length == 1);
        assert(dfTarget[0][0] == 11);
        dfTarget.push();
        assert(dfTarget[1].length == 2);
        assert(dfTarget[1][0] == 0);
        assert(dfTarget[1][1] == 0);
    }

    function dynamicDynamicShrinkClearsReusedRow() public {
        delete dd;
        dd.push();
        dd[0].push(11);
        delete ddTarget;
        ddTarget.push();
        ddTarget.push();
        ddTarget[1].push(99);
        ddTarget = dd;
        assert(ddTarget.length == 1);
        assert(ddTarget[0][0] == 11);
        ddTarget.push();
        assert(ddTarget[1].length == 0);
        ddTarget[1].push();
        assert(ddTarget[1][0] == 0);
    }

    function fixedMemoryRowsToDynamicStorageOuter() public {
        uint[2][2] memory m;
        m[0][0] = 11;
        m[0][1] = 12;
        m[1][0] = 21;
        m[1][1] = 22;
        delete df;
        df.push();
        df.push();
        df[0][0] = 71;
        df[0][1] = 72;
        df[1][0] = 81;
        df[1][1] = 82;
        df = m;
        m[0][0] = 99;
        assert(df.length == 2);
        assert(df[0].length == 2);
        assert(df[0][0] == 11);
    }
}
