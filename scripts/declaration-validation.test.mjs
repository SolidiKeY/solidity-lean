import { test } from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, writeFileSync, rmSync } from 'node:fs';
import { join } from 'node:path';
import { tmpdir } from 'node:os';
import { runSolidityTests, testsPassed } from './test-solidity.mjs';

test('invalid specification syntax is local in mixed reports and an error for an unusable selection', () => {
  const dir = mkdtempSync(join(tmpdir(), 'solidity-spec-diagnostic-'));
  try {
    const file = join(dir, 'ClauseDiagnostics.sol');
    writeFileSync(file, `pragma solidity ^0.8.0;
contract ClauseDiagnostics {
    /// @custom:key ensures true
    function valid() public pure {}
    /// @custom:key ensures false
    function falseProperty() public pure {}
    /// @custom:key ensures false; requires false
    function bad() public pure {}
    /// @custom:key requires from == 7
    /// @custom:key ensures false; requires false
    function renamed(uint from) public pure { assert(false); }
    /// @custom:key ensures true
    function caller() public pure { bad(); }
    function assemblyGap() public pure { assembly { mstore(0, 1) } }
}`);
    const mixed = runSolidityTests([file], {build:false, batchSize:1});
    assert.deepEqual(mixed.errors, []);
    assert.equal(mixed.results.length, 6);
    const rows = Object.fromEntries(mixed.results.map(row => [row.function, row]));
    assert.equal(rows.valid.status, 'proved');
    assert.equal(rows.falseProperty.status, 'pending');
    for (const name of ['bad', 'renamed', 'caller']) {
      assert.equal(rows[name].status, 'unsupported');
      assert.equal(rows[name].invalidSpecification, true);
      assert.match(rows[name].reason, /expected end of input/);
      const only = runSolidityTests([file], {build:false, function:name});
      assert.equal(only.results.length, 1);
      assert.equal(only.results[0].status, 'unsupported');
      assert.equal(only.errors.length, 1);
      assert.equal(only.errors[0].stage, 'specification');
      assert.equal(testsPassed(only), false);
    }
    const assembly = runSolidityTests([file], {build:false, function:'assemblyGap'});
    assert.deepEqual(assembly.errors, []);
    assert.equal(assembly.results[0].status, 'excluded');
    assert.equal(assembly.results[0].invalidSpecification, false);
    assert.equal(testsPassed(mixed), false);
  } finally { rmSync(dir, {recursive:true, force:true}); }
});
