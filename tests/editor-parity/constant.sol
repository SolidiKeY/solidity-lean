// SPDX-License-Identifier: MIT
pragma solidity ^0.8.34;
contract Parity {
  /// @custom:key ensures \result == 1
  function f0() public pure returns (uint256 result) { return 1; }
  /// @custom:key ensures \result == 2
  function f1() public pure returns (uint256 result) { return 1; }
}
