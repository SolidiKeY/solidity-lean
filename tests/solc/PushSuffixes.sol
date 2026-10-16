// SPDX-License-Identifier: GPL-3.0
pragma solidity ^0.8.0;

contract PushSuffixes {
    int[] values;
    uint[] unsignedValues;
    int[][] matrix;
    uint cursor;
    int seen;
    uint[][] unsignedMatrix;
    uint se1;

    function next() internal returns (uint) { ++seen; return cursor++; }
    function rhs() internal returns (int) { ++cursor; return 3; }
    function nextFresh() internal returns (uint) { ++se1; return 0; }

    function signedOps() public {
        delete values;
        values.push() += 3;
        values.push() -= 2;
        values.push() *= 7;
        values.push() /= 2;
        values.push() %= 2;
        ++values.push();
        values.push()++;
        --values.push();
        values.push()--;
        assert(values.length == 9);
        assert(values[0] == 3 && values[1] == -2);
        assert(values[2] == 0 && values[3] == 0 && values[4] == 0);
        assert(values[5] == 1 && values[6] == 1);
        assert(values[7] == -1 && values[8] == -1);
    }

    function unsignedOps() public {
        delete unsignedValues;
        unsignedValues.push() += 3;
        unsignedValues.push() -= 0;
        unsignedValues.push() *= 7;
        unsignedValues.push() /= 2;
        unsignedValues.push() %= 2;
        ++unsignedValues.push();
        unsignedValues.push()++;
        assert(unsignedValues.length == 7);
        assert(unsignedValues[0] == 3 && unsignedValues[1] == 0);
        assert(unsignedValues[2] == 0 && unsignedValues[3] == 0 && unsignedValues[4] == 0);
        assert(unsignedValues[5] == 1 && unsignedValues[6] == 1);
    }

    function nestedOps() public {
        delete matrix;
        matrix.push();
        matrix[0].push() += 3;
        matrix[0].push() -= 2;
        matrix[0].push() *= 7;
        matrix[0].push() /= 2;
        matrix[0].push() %= 2;
        ++matrix[0].push();
        matrix[0].push()++;
        --matrix[0].push();
        matrix[0].push()--;
        assert(matrix[0].length == 9);
        assert(matrix[0][0] == 3 && matrix[0][1] == -2);
        assert(matrix[0][5] == 1 && matrix[0][6] == 1);
        assert(matrix[0][7] == -1 && matrix[0][8] == -1);
    }

    function effectfulIndex() public {
        delete matrix;
        matrix.push();
        matrix.push();
        cursor = 0;
        matrix[cursor++].push() += rhs();
        assert(cursor == 2 && matrix[0].length == 0 && matrix[1][0] == 3);
    }

    function effectfulCall() public {
        delete matrix;
        matrix.push();
        cursor = 0;
        seen = 0;
        matrix[next()].push() += seen;
        assert(cursor == 1 && seen == 1 && matrix[0][0] == 0);
    }

    function recycled() public {
        values.push() += 3;
        assert(values[0] == 3);
    }

    function falsePost() public {
        delete values;
        values.push() += 3;
        assert(values[0] == 4);
    }

    function zeroDivisor() public { values.push() /= 0; }
    function zeroRemainder() public { values.push() %= 0; }
    function preUnderflow() public { --unsignedValues.push(); }
    function postUnderflow() public { unsignedValues.push()--; }

    function freshLocal() public {
        delete unsignedMatrix;
        unsignedMatrix.push();
        uint se2 = 0;
        unsignedMatrix[se2++].push() += se2;
        assert(se2 == 1 && unsignedMatrix[0][0] == 0);
    }
    function freshLocalFalse() public {
        delete unsignedMatrix;
        unsignedMatrix.push();
        uint se2 = 0;
        unsignedMatrix[se2++].push() += se2;
        assert(unsignedMatrix[0][0] == 1);
    }
    function freshParameter(uint ie1) public {
        delete unsignedMatrix;
        unsignedMatrix.push();
        unsignedMatrix[ie1++].push() += ie1;
        assert(ie1 == 1 && unsignedMatrix[0][0] == 0);
    }
    function freshParameterFalse(uint ie1) public {
        delete unsignedMatrix;
        unsignedMatrix.push();
        unsignedMatrix[ie1++].push() += ie1;
        assert(unsignedMatrix[0][0] == 1);
    }
    function freshState() public {
        delete unsignedMatrix;
        unsignedMatrix.push();
        se1 = 0;
        unsignedMatrix[nextFresh()].push() += se1;
        assert(se1 == 1 && unsignedMatrix[0][0] == 0);
    }
    function freshStateFalse() public {
        delete unsignedMatrix;
        unsignedMatrix.push();
        se1 = 0;
        unsignedMatrix[nextFresh()].push() += se1;
        assert(unsignedMatrix[0][0] == 1);
    }
    function freshBinary() public {
        uint ie1 = 0;
        uint result = ie1++ + ie1;
        assert(result == 0 && ie1 == 1);
    }
    function freshBinaryFalse() public {
        uint ie1 = 0;
        uint result = ie1++ + ie1;
        assert(result == 1);
    }
}
