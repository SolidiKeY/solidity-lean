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
  function invariantForCountsArrayLength() public view {
    uint c = 0;
    /// @custom:key invariant 0 <= i && i <= values.length && c == i
    for (uint i = 0; i < values.length; i++)
    {
      c = c + 1;
    }
    assert(c == values.length);
  }
}
