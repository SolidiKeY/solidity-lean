import {test} from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {runSolidityTests, testsPassed} from './test-solidity.mjs';

test('finite primitive membership compiles source specifications into checked proofs', () => {
  const report = runSolidityTests(['tests/solc/FiniteSets.sol'], {build:false, contract:'FiniteSets'});
  assert.deepEqual(report.errors, []);
  const results = new Map(report.results.map(row => [row.function, row]));
  for (const name of ['echo','negative','truth','addressChoice','empty','snapshot','store','renamed','dollars','quantifiedShadow','ledgerComparison'])
    assert.equal(results.get(name)?.status, 'proved', `${name}: ${results.get(name)?.reason}`);
  assert.equal(results.get('falsePost')?.status, 'pending');
  assert.equal(results.get('falseEmpty')?.status, 'pending');
  const hash = createHash('sha256').update(readFileSync('tests/solc/FiniteSets.sol')).digest('hex');
  assert.ok(report.results.every(row => row.sourceHash === hash));
  assert.ok(report.results.every(row => row.sourceId >= 0 && row.range));
  assert.equal(testsPassed(report), false);
});

test('invalid finite membership operands never become successful or vacuous proofs', () => {
  const report = runSolidityTests(['tests/solc/FiniteSets.sol'], {build:false, contract:'InvalidFiniteSets'});
  const names = ['unknownEmpty','forbiddenOld','mixed','fixedMixed','ledgerKey','ledgerItem','numericBool','negativeUint','largeLiteral','unknownItem','referenceEmpty'];
  assert.deepEqual(report.results.map(row => row.function).sort(), [...names].sort());
  for (const row of report.results) {
    assert.equal(row.status, 'error', `${row.function}: ${row.status} ${row.reason}`);
    assert.ok(row.reason.length, row.function);
  }
  assert.ok(report.errors.length > 0, 'Lean must retain the specification elaboration diagnostics');
  assert.equal(testsPassed(report), false);
});
