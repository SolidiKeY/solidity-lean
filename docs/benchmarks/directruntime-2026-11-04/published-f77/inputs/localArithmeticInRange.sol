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
  function localArithmeticInRange(uint x) public pure {
    require(x >= 1 && x <= 100);
    uint r;
    r = x + 1;
    r -= 1;
    ++r;
    assert(r == x + 1);
  }
}
