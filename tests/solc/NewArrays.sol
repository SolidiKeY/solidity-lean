// SPDX-License-Identifier: GPL-3.0
pragma solidity ^0.8.0;
contract NewArrays {
    uint[] values;
    uint[][] matrix;
    uint[3][] rows;
    function storageRoot() public {
        values = new uint[](3);
        assert(values.length == 3 && values[2] == 0);
    }
    function nestedDefaults() public {
        matrix = new uint[][](2);
        assert(matrix.length == 2);
        assert(matrix[1].length == 0);
        rows = new uint[3][](2);
        assert(rows.length == 2);
        assert(rows[1].length == 3);
        assert(rows[1][2] == 0);
    }
    function sizeOnce() public {
        uint n = 2;
        values = new uint[](n++);
        assert(n == 3 && values.length == 2 && values[1] == 0);
    }
    function memorySizeOnce() public pure {
        uint n = 2;
        uint[] memory local = new uint[](n++);
        assert(n == 3 && local.length == 2 && local[1] == 0);
    }
    function receiverAfterSize() public {
        matrix = new uint[][](2);
        uint i = 1;
        matrix[i++] = new uint[](i);
        assert(i == 2 && matrix[1].length == 1);
    }
    /// @custom:key box
    function symbolicSize(uint n) public {
        require(n > 0);
        values = new uint[](n);
        assert(values.length == n && values[n - 1] == 0);
    }
    function falsePost() public {
        values = new uint[](3);
        assert(values[2] == 1);
    }
    function emptyRead() public {
        values = new uint[](0);
        assert(values[0] == 0);
    }
}
