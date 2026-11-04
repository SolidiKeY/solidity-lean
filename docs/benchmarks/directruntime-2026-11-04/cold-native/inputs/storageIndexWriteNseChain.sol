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
  function storageIndexWriteNseChain(uint i, uint x, uint y) public {
    require(i == 2 && x == 3 && y == 4);
    balances[i + 1] = x * y + 3;
    uint r = balances[3];
    assert(r == 15);
  }
}
