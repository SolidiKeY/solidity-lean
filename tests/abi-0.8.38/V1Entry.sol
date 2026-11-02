// SPDX-License-Identifier: GPL-3.0
// Lane FU2-C: ABI coder v1 cleans value parameters instead of validating them.
pragma solidity ^0.8.0;
pragma abicoder v1;
contract V1Entry {
  function k(uint8 a, int16 b, bool c, bytes3 d, address e) public pure returns (uint8, int16, bool, bytes3, address) { return (a, b, c, d, e); }
  function u(uint16 a) public pure returns (uint256) { return a; }
  function s(int8 a) public pure returns (int256) { return a; }
  function bo(bool a) public pure returns (uint256) { return a ? 7 : 3; }
}
