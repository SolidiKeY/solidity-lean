import {test} from 'node:test';
import assert from 'node:assert/strict';
import {runSolidityTests} from './test-solidity.mjs';

function rows(report) {
  assert.deepEqual(report.errors, [], 'compiler/import/proof infrastructure must succeed');
  return new Map(report.results.map(row => [row.function, row]));
}

// These are integration gates for the primary chat, not evidence that the
// patch worker ran Lean. No expected result in the existing suite is weakened.
test('checked cancellation preserves sum definedness in both operand orders', () => {
  const byName = rows(runSolidityTests(['tests/solc/GuardedCancellation.sol'],
    {build:false, contract:'GuardedCancellation'}));
  for (const name of ['leftUint', 'rightUint', 'leftInt', 'rightInt']) {
    assert.ok(byName.has(name), name);
    assert.equal(byName.get(name).status, 'proved', `${name}: ${byName.get(name).reason}`);
  }
  for (const name of ['overflowingUint', 'overflowingInt', 'wrongUint']) {
    assert.ok(byName.has(name), name);
    // Refutation is useful evidence. Pending is honest incompleteness; import
    // refusal, absence of an obligation, and a false proof are all failures.
    assert.ok(['refuted', 'pending'].includes(byName.get(name).status),
      `${name}: ${byName.get(name).status}: ${byName.get(name).reason}`);
  }
});

test('external selector projection and original indirect-call regression', () => {
  const byName = rows(runSolidityTests(['tests/solc/FunctionTypes.sol'],
    {build:false, contract:'ExternalFunctionTypes'}));
  assert.equal(byName.get('selectorOfValue')?.status, 'proved');
  assert.equal(byName.get('externalSelector')?.status, 'proved');
  // Keep the original target as a hard integration gate. If it still fails,
  // inspect its residual goals rather than weakening the expected verdict.
  assert.equal(byName.get('externalValue')?.status, 'proved',
    byName.get('externalValue')?.reason);
  assert.ok(['refuted', 'pending'].includes(byName.get('falseSelectorOfValue')?.status));
});
