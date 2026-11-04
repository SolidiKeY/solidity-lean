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
  function whileBodyDeclaresLocal() public pure {
    uint i = 0;
    uint s = 0;
    /// @custom:key invariant (i == 0 && s == 0) || (i == 1 && s == 0) || (i == 2 && s == 2) || (i == 3 && s == 6)
    while (i < 3)
    {
      uint t = i * 2;
      s = s + t;
      i = i + 1;
    }
    assert(s == 6);
  }
}
