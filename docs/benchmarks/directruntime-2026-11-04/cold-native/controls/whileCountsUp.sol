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
  function whileCountsUp() public pure {
    uint i = 0;
    /// @custom:key invariant i <= 3
    while (i < 3)
    {
      i = i + 1;
    }
    assert(i == 4);
  }
}
