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
  function storageMatrixWriteRead() public {
    require(2 < matrix.length);
    require(3 < matrix[2].length);
    matrix[2][3] = 99;
    uint r = matrix[2][3];
    assert(r == 99);
  }
}
