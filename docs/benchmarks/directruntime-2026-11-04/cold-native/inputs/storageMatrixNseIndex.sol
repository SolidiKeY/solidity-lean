// SPDX-License-Identifier: MIT
pragma solidity ^0.8.34;
contract TestSuite {

  uint age;
  uint balance;
  uint total;
  bool flag;
  uint[] values;
  uint[][] matrix;
  mapping(uint => uint) balances;
  mapping(uint => bool) flags;
  mapping(uint => uint) valuesMap;
  mapping(uint => mapping(uint => uint)) grid;
  mapping(bool => uint) boolKeyed;



  /// @custom:key box
  function storageMatrixNseIndex(uint i, uint j, uint x, uint y) public {
    require(2 < matrix.length);
    require(3 < matrix[2].length);
    require(i == 1 && j == 2 && x == 5 && y == 6);
    matrix[i + 1][j + 1] = x + y;
    assert(matrix[2][3] == 11);
  }
}
