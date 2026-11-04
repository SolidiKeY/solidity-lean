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
  function testStorageMapReadWriteAndDelete() public {
    valuesMap[1] = 10;
    valuesMap[2] = 20;
    uint v = valuesMap[1];
    uint kept = valuesMap[2];
    delete valuesMap[1];
    assert(v == 10);
    assert(kept == 20);
    assert(valuesMap[1] == 0);
    assert(valuesMap[2] == 20);
  }
}
