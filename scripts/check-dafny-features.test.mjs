import { readFileSync } from 'node:fs';
import assert from 'node:assert/strict';
import { test } from 'node:test';
import { validateManifest } from './check-dafny-features.mjs';

const original = JSON.parse(readFileSync(new URL('../docs/dafny-features.json', import.meta.url), 'utf8'));
const copy = () => structuredClone(original);

test('checked inventory retains evidence files and all reference chapters', () => {
  assert.deepEqual(validateManifest(original), []);
});

test('removing or duplicating a family cannot silently reduce coverage', () => {
  const missing = copy();
  missing.features.shift();
  assert.ok(validateManifest(missing).some(e => e === 'missing feature family: preconditions'));
  const duplicate = copy();
  duplicate.features.push(duplicate.features[0]);
  assert.ok(validateManifest(duplicate).some(e => e === 'duplicate feature family: preconditions'));
});

test('upstream evidence must belong to the pinned inspected inventory', () => {
  const m = copy();
  m.upstream.commit = '0'.repeat(40);
  m.features[0].upstream[0] = {path: 'docs/DafnyRef/Unreviewed.md', line: 0};
  const errors = validateManifest(m);
  assert.ok(errors.some(e => e.includes('unexpected upstream commit')));
  assert.ok(errors.some(e => e.includes('uninspected upstream evidence')));
  assert.ok(errors.some(e => e.includes('invalid upstream line')));
});

test('stale and escaping local evidence paths fail offline', () => {
  for (const path of ['Solidity/DoesNotExist.lean', '../outside', '/etc/passwd', 'docs\\README.md', 'docs/../README.md']) {
    const m = copy();
    m.features[0].localEvidence = [path];
    assert.ok(validateManifest(m).some(e => /local evidence/.test(e)), path);
  }
});

test('dropping chapter evidence or source provenance fails', () => {
  const m = copy();
  m.upstream.sources.shift();
  m.features.find(f => f.id === 'modules-refinement').upstream.pop();
  const errors = validateManifest(m);
  assert.ok(errors.some(e => e.includes('missing inspected source')));
  assert.ok(errors.some(e => e === 'uncited reference chapter: Refinement'));
});

test('malformed entries and unsupported status never count as reviewed', () => {
  const m = copy();
  m.features[0].status = 'fully-proved';
  m.upstream.inspectedOn = '2026-02-30';
  m.features.push(null);
  m.upstream.sources.push(null);
  assert.ok(validateManifest(m).some(e => e === 'invalid status: preconditions'));
  assert.ok(validateManifest(m).includes('invalid inspection date'));
  assert.ok(validateManifest(null).includes('manifest must be an object'));
  assert.ok(validateManifest({}).includes('features must be an array'));
});
