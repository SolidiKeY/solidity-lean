// SPDX-License-Identifier: MIT
pragma solidity ^0.8.34;
contract HoverCases {
  uint256 public x;
  /// @notice Add values.
  /// @param a Left input.
  function helper(uint256 a) public pure returns (uint256) { return a; }
  function run() public view returns (uint256) {
    bool x = true;
    { uint256 x = 1; uint256 inside = x; }
    bool outside = x;
    return this.helper(this.x());
  }
}
