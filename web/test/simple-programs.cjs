'use strict';
// Identical programs for the Java SolKey and native/browser Lean measurements.
const program=(name,declarations,status='proved')=>({name,status,source:`// SPDX-License-Identifier: MIT
pragma solidity ^0.8.34;
contract Simple {
${declarations}
}
`});
module.exports=[
  program('constant',String.raw`  /// @custom:key ensures \result == 1
  function run() public pure returns (uint result) { return 1; }`),
  program('identity',String.raw`  /// @custom:key ensures \result == x
  function run(uint x) public pure returns (uint result) { return x; }`),
  program('assignment',String.raw`  uint value;
  /// @custom:key ensures value == x
  function run(uint x) public { value = x; }`),
  program('increment',String.raw`  uint value;
  /// @custom:key ensures value == \old(value) + 1
  function run() public { value = value + 1; }`),
  program('branch',String.raw`  /// @custom:key ensures \result >= x
  function run(uint x, uint y) public pure returns (uint result) {
    if (x >= y) return x;
    return y;
  }`),
  program('false-constant',String.raw`  /// @custom:key ensures \result == 1
  function run() public pure returns (uint result) { return 2; }`,'pending'),
];
