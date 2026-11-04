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
  function forWritesStorageArray() public {
    require(values.length == 3);
    /// @custom:key invariant i <= values.length && values.length == 3
    /// @custom:key invariant \forall uint j; j < i -> values[j] == j * j
    for (uint i = 0; i < values.length; i++)
    {
      values[i] = i * i;
    }
    assert(values[2] == 4);
  }
}
