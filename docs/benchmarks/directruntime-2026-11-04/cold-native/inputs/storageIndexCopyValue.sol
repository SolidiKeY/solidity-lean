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
  function storageIndexCopyValue(uint i, uint j) public {
    require(1 < values.length);
    require(i == 5 && j == 1);
    values[1] = 8;
    balances[i] = values[j];
    uint r = balances[5];
    assert(r == 8);
  }
}
