import {test} from 'node:test';
import assert from 'node:assert/strict';
import {runSolidityTests} from './test-solidity.mjs';

// Integrator: build Solidity.Frontend.Testing first. This test does no build.
test('typed source transient operations at a deployed address preserve both regions', () => {
  const report = runSolidityTests(['tests/solc/TransientSource.sol'], {build:false, selfAddress:1});
  const rows = report.results.filter(r => r.contract === 'TransientSource');
  for (const name of ['ordinary', 'selfSharing', 'rollback']) {
    assert.equal(rows.find(r => r.function === name)?.status, 'proved', JSON.stringify(report));
  }
  assert.equal(rows.find(r => r.function === 'falsePersistentAlias')?.status, 'pending', JSON.stringify(report));
  assert.equal(report.results.find(r => r.contract === 'TransientDerived' &&
    r.function === 'inheritedOperations')?.status, 'proved', JSON.stringify(report));
  assert.equal(report.errors.length, 0, JSON.stringify(report));
});

test('unused, getter and inherited transient headers are retained', () => {
  const report = runSolidityTests(['tests/solc/TransientStorage.sol'], {build:false});
  for (const contract of ['TransientHeader','InheritedTransientHeader']) {
    assert.equal(report.errors.some(e => e.contract === contract), false, JSON.stringify(report));
    // The report lists own declarations; the empty derived header has no rows.
    if (contract === 'TransientHeader') assert.equal(report.results.find(r =>
      r.contract === contract && r.function === 'ordinary')?.status, 'proved', JSON.stringify(report));
  }
  assert.equal(report.results.find(r => r.contract === 'TransientStorage' &&
    r.function === 'staticWrite')?.status, 'excluded', JSON.stringify(report));
  const control = report.results.filter(r => r.contract === 'TransientPersistentControl');
  assert.equal(control.find(r => r.function === 'ordinary')?.status, 'proved', JSON.stringify(report));
  assert.equal(control.find(r => r.function === 'falseClaim')?.status, 'pending', JSON.stringify(report));
  assert.equal(report.errors.some(e => e.contract === 'TransientPersistentControl'), false, JSON.stringify(report));
});
