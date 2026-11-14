import test from 'node:test';
import assert from 'node:assert/strict';
import {runTool} from './test-solidity.mjs';
// Explicit integration target: requires the normal pinned compiler/Lean setup.
// The fixture preserves the complete adapted U01 case; it does not admit a suite.
test('compiled invariant leaves agree with the unchanged certified obligation',()=>{
  const output=runTool(process.execPath,['scripts/verify.mjs',
    'scripts/verify-fixtures/InvariantLeaves.sol','--mode','fast','--compare','--json',
    '--contract','TestSuite','--function','whileCountsUp'],600000);
  const report=JSON.parse(output);
  assert.equal(report.status,'agree');assert.equal(report.obligations,1);
  assert.equal(report.fast.results[0].status,'proved');
  assert.equal(report.fast.results[0].verification,'native');
  assert.equal(report.certified.results[0].status,'proved');
  assert.equal(report.certified.results[0].verification,'certified');
  assert.equal(report.fast.results[0].reading,'clean');
  assert.equal(report.certified.results[0].reading,'clean');
  assert.equal(report.fast.results[0].sourceHash,report.certified.results[0].sourceHash);
});
