'use strict';

/** The shared fragment uses constants within uint256, avoiding overflow and
 * Dafny's unbounded-integer/termination semantics. Obligations are paired by
 * ordinal, never by a source range that belongs to a different language. */
function workload(target, count = 8, failing = false) {
  if (!Number.isSafeInteger(count) || count < 1 || count > 1000) throw new Error('Invalid workload size');
  const expected = failing ? 2 : 1;
  const declarations = Array.from({length:count},(_,i)=> target === 'dafny'
    ? `method f${i}() returns (r: int)\n  ensures r == ${expected}\n{ r := 1; }`
    : `  /// @custom:key ensures \\result == ${expected}\n  function f${i}() public pure returns (uint256 result) { return 1; }`);
  return target === 'dafny' ? declarations.join('\n')+'\n' : `// SPDX-License-Identifier: MIT\npragma solidity ^0.8.34;\ncontract Parity {\n${declarations.join('\n')}\n}\n`;
}
function symbolPosition(target, text, ordinal = 0) {
  const lines = text.split('\n');
  const line = lines.findIndex(s => s.includes(`f${ordinal}(`));
  return {line,character:lines[line].indexOf(`f${ordinal}`)};
}
module.exports = {workload,symbolPosition};
