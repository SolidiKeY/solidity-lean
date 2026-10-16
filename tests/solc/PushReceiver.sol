// SPDX-License-Identifier: GPL-3.0
pragma solidity ^0.8.0;
contract PushReceiver {
    uint[][] matrix;
    /// @custom:key box
    function nested() public {
        delete matrix;
        matrix.push();
        matrix[0].push(4);
        uint y = matrix[0].push();
        assert(y == 0);
        assert(matrix[0].length == 2);
        y = matrix[0].push();
        assert(y == 0);
        assert(matrix[0].length == 3);
    }
    /// @custom:key box
    function falsePost() public {
        delete matrix;
        matrix.push();
        uint y = matrix[0].push();
        assert(y == 1);
    }
    /// @custom:key box
    function effectfulReceiver() public {
        delete matrix;
        matrix.push();
        matrix.push();
        uint i = 0;
        uint y = matrix[i++].push();
        assert(i == 1 && y == 0);
        assert(matrix[0].length == 1 && matrix[1].length == 0);
        y = matrix[i++].push();
        assert(i == 2 && y == 0);
        assert(matrix[0].length == 1 && matrix[1].length == 1);
    }
    /// @custom:key box
    function oldTargetIndex() public {
        delete matrix;
        matrix.push();
        matrix.push();
        uint y = 1;
        y = matrix[y + 0].push();
        assert(y == 0);
        assert(matrix[0].length == 0 && matrix[1].length == 1);
    }
    /// @custom:key box
    function falseTargetIndex() public {
        delete matrix;
        matrix.push();
        matrix.push();
        uint y = 1;
        y = matrix[y + 0].push();
        assert(matrix[0].length == 1);
    }
}
