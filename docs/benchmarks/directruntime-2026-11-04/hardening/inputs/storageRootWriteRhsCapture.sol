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
  function storageRootWriteRhsCapture(uint x, uint y, uint z) public {
    require(x == 1 && y == 2 && z == 3);
    total = x + y * z;
    uint r = total;
    assert(r == 7);
  }
}
