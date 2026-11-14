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

test('compiled recursion executes the walk and closer without declaring a result theorem',()=>{
  const report=JSON.parse(runTool(process.execPath,['scripts/verify.mjs',
    'tests/solc/Recursion.sol','--mode','fast','--compare','--json','--function','countdown'],600000));
  assert.equal(report.status,'agree');
  const row=report.fast.results[0];
  assert.equal(row.status,'proved');assert.equal(row.verification,'native');
  for(const probe of ['command','rec_auto','closing'])assert.ok(row.nativeCProbes.includes(probe));
});

test('callback discovery preserves the certified per-function solc reading',()=>{
  const report=JSON.parse(runTool(process.execPath,['scripts/verify.mjs',
    'scripts/verify-fixtures/CallbackDiscovery.sol','--mode','fast','--compare','--json',
    '--function','localKept'],600000));
  assert.equal(report.status,'agree');
  const row=report.fast.results[0];
  assert.equal(row.status,'proved');assert.equal(row.verification,'native');
  assert.equal(row.reading,'solc');assert.equal(report.certified.results[0].reading,'solc');
  assert.ok(row.nativeCProbes.includes('sol_prove'));
});
