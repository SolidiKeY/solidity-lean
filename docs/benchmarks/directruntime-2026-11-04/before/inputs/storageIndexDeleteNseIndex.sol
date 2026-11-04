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
  function storageIndexDeleteNseIndex(uint k) public {
    require(k == 2);
    balances[3] = 7;
    delete balances[k + 1];
    uint r = balances[3];
    assert(r == 0);
  }
}
