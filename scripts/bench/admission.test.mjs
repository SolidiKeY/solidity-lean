// Guard U01 against interpreting admission readiness, partial runs or refusals as verification.
import test from 'node:test';
import assert from 'node:assert/strict';
import {admissionResult} from './admission.mjs';

test('ready rows establish listing only, never verification', () => {
  const row = {function: 'transfer', signature: 'transfer(address,uint256)', status: 'ready', reading: 'solc'};
  const result = admissionResult({results: [row], errors: []}, true);
  assert.equal(result.listingPassed, true);
  assert.equal(result.verification, 'not-run');
  assert.equal(result.sourceToVerdictBaseline, false);
  assert.deepEqual(result.results, [row]);
});

test('refusals and compiler/tool errors remain visible in a mixed report', () => {
  const rows = [{function: 'f', status: 'ready'}, {function: 'f', signature: 'f(uint)', status: 'unsupported', reason: 'unsupported body'}];
  const errors = [{stage: 'compile', reason: 'compiler failed'}];
  const result = admissionResult({results: rows, errors}, true);
  assert.equal(result.listingPassed, false);
  assert.equal(result.rows, 2);
  assert.equal(result.readyRows, 1);
  assert.deepEqual(result.results, rows);
  assert.deepEqual(result.errors, errors);
});

test('empty, skipped-only and interrupted attempts cannot pass', () => {
  for (const rows of [[], [{status: 'skip'}], [{status: 'proved'}]])
    assert.equal(admissionResult({results: rows, errors: []}, true).listingPassed, false);
  assert.equal(admissionResult({results: [{status: 'ready'}], errors: []}, false).listingPassed, false);
});
