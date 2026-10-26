import {test} from 'node:test';
import assert from 'node:assert/strict';
import {runSolidityTests} from './test-solidity.mjs';

// Integrator: build Solidity.Frontend.Testing first. This test does no build.
test('transient declarations never silently become persistent roots', () => {
  const report = runSolidityTests(['tests/solc/TransientStorage.sol'], {build:false});
  for (const contract of ['TransientStorage','TransientHeader','InheritedTransientHeader']) {
    assert(report.errors.some(e => e.contract === contract && /transient/i.test(e.reason)),
      JSON.stringify(report));
    assert.equal(report.results.some(r => r.contract === contract), false,
      'a transient contract must be refused as a whole, including getters and unused declarations');
  }
  const control = report.results.filter(r => r.contract === 'TransientPersistentControl');
  assert.equal(control.find(r => r.function === 'ordinary')?.status, 'proved', JSON.stringify(report));
  assert.equal(control.find(r => r.function === 'falseClaim')?.status, 'pending', JSON.stringify(report));
  assert.equal(report.errors.some(e => e.contract === 'TransientPersistentControl'), false, JSON.stringify(report));
});
