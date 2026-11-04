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
  function storagePushNonsimpleArg(uint x, uint y) public {
    require(values.length == 2);
    require(x == 40 && y == 2);
    values.push(x + y);
    assert(values[2] == 42);
    assert(values.length == 3);
  }
}
