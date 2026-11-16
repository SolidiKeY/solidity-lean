// Guard U01 against interpreting admission readiness, partial runs or refusals as verification.
import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import {fileURLToPath} from 'node:url';
import {spawnSync} from 'node:child_process';
import {sourceHash} from '../source-locations.mjs';
import {admissionResult, sourceIdentityErrors} from './admission.mjs';

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


test('failed input discovery replaces an old successful report without invoking Lean', () => {
  const directory = fs.mkdtempSync(path.join(os.tmpdir(), 'u01-admission-control-'));
  try {
    const output = path.join(directory, 'report.json');
    fs.writeFileSync(output, JSON.stringify({listingPassed: true, results: [{status: 'ready'}]}));
    const run = spawnSync(process.execPath, [fileURLToPath(new URL('./admission.mjs', import.meta.url)),
      '--out', output, path.join(directory, 'missing.sol')], {encoding: 'utf8'});
    assert.equal(run.status, 1, run.stderr);
    const result = JSON.parse(fs.readFileSync(output, 'utf8'));
    assert.equal(result.listingPassed, false);
    assert.equal(result.attemptFinished, true);
    assert.deepEqual(result.results, []);
    assert.equal(result.errors[0].stage, 'admission');
    assert.equal(result.selection.paths[0], path.join(directory, 'missing.sol'));
  } finally { fs.rmSync(directory, {recursive: true, force: true}); }
});

test('compiled-row identity and final bytes must both match the initial snapshot', () => {
  const original = Buffer.from('contract A {}');
  const changed = Buffer.from('contract B {}');
  const source = '/fixture/A.sol';
  const inputs = [{path: source, sha256: sourceHash(original)}];
  const row = {source, sourceHash: sourceHash(original), function: 'f', status: 'ready'};
  assert.deepEqual(sourceIdentityErrors(inputs, [row], () => original), []);
  for (const errors of [
    sourceIdentityErrors(inputs, [{...row, sourceHash: sourceHash(changed)}], () => original),
    sourceIdentityErrors(inputs, [row], () => changed),
    sourceIdentityErrors(inputs, [{...row, source: '/fixture/unknown.sol'}], () => original),
  ]) {
    assert.ok(errors.length > 0);
    assert.ok(errors.every(error => error.stage === 'source-identity'));
    assert.equal(admissionResult({results: [row], errors}, true).listingPassed, false);
  }
});


test('admission output cannot overwrite Solidity input files', () => {
  const directory = fs.mkdtempSync(path.join(os.tmpdir(), 'u01-admission-control-'));
  try {
    const source = path.join(directory, 'source.sol');
    const content = 'contract C {}'; fs.writeFileSync(source, content);
    const run = spawnSync(process.execPath, [fileURLToPath(new URL('./admission.mjs', import.meta.url)),
      '--out', source, source], {encoding: 'utf8'});
    assert.equal(run.status, 2, run.stderr);
    assert.equal(fs.readFileSync(source, 'utf8'), content);
  } finally { fs.rmSync(directory, {recursive: true, force: true}); }
});
