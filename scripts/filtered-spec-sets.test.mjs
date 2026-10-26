import {test} from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {runSolidityTests, testsPassed} from './test-solidity.mjs';

const fixture = 'tests/solc/FilteredSets.sol';

test('filtered finite membership preserves typed binders, snapshots and checked source proofs', () => {
  const report = runSolidityTests([fixture], {build:false, contract:'FilteredSets'});
  assert.deepEqual(report.errors, []);
  const rows = new Map(report.results.map(row => [row.function, row]));
  assert.equal(report.results.length, rows.size, 'source rows must be unique');
  const proved = ['echo','negative','truth','addressChoice','empty','falseGuard','duplicate',
    'outerKey','outerGuard','dollars','inheritedConstantShadow','stateNameShadow','quantifiedShadow','nested','oldGuard',
    'oldWhole','oldKey','oldLedger','undefinedKey','guardTheoryEquality','resultReference'];
  assert.equal(rows.size, proved.length + 3);
  for (const name of proved)
    assert.equal(rows.get(name)?.status, 'proved', `${name}: ${JSON.stringify(rows.get(name))}`);
  for (const name of ['witness','falsePost','falseOuterGuard'])
    assert.equal(rows.get(name)?.status, 'pending', name);
  const hash = createHash('sha256').update(readFileSync(fixture)).digest('hex');
  assert.ok(report.results.every(row => row.sourceHash === hash && row.sourceId >= 0 && row.range));
  assert.equal(testsPassed(report), false);
});

test('invalid filtered domains and empty operands fail before becoming vacuous proofs', () => {
  const report = runSolidityTests([fixture], {build:false, contract:'InvalidFilteredSets'});
  const names = ['unknownEmptyKey','unknownEmptyGuard','forbiddenOld','nestedOld','numericGuard',
    'dynamicDomain','capturedDomain','arithmeticDomain','ledgerDomain','ledgerKey','negativeUint','fixedMixed',
    'mixedBool','numericBool','largeDomain','largeEmptyKey','referenceKey','oldMemory','loopBoundary',
    'shadowedArrayLength','shadowedEmptyArrayLength','shadowedMapping','shadowedStruct','shadowedMemory',
    'reservedResult','reservedOld','reservedOldNet','reservedNamedReturn','nestedReservedResult'];
  assert.deepEqual(report.results.map(row => row.function).sort(), [...names].sort());
  for (const row of report.results) {
    assert.equal(row.status, row.function === 'loopBoundary' ? 'unsupported' : 'error',
      `${row.function}: ${row.status} ${row.reason}`);
    assert.ok(row.reason.length, row.function);
  }
  assert.match(report.results.find(row => row.function === 'loopBoundary').reason,
    /filtered finite membership.*loop/i);
  assert.ok(report.errors.length > 0);
  assert.equal(testsPassed(report), false);
});

test('a satisfiable filtered precondition yields an exact certified source counterexample', () => {
  const report = runSolidityTests([fixture],
    {build:false, contract:'FilteredSets', function:'witness(bool)', counterexamples:true});
  assert.deepEqual(report.errors, []);
  assert.equal(report.results.length, 1);
  const row = report.results[0];
  assert.equal(row.status, 'refuted', JSON.stringify(row));
  const witness = row.counterexample;
  assert.equal(witness?.kind, 'model-state');
  assert.equal(witness.certified, true);
  assert.equal(witness.goalKind, 'fmlValid');
  assert.equal(typeof witness.certificateDeclaration, 'string');
  assert.deepEqual(witness.arguments.map(arg => [arg.sourceName, arg.paramIndex, arg.type, arg.value]),
    [['flag', 0, 'bool', true]]);
  assert.ok(witness.axioms.every(name => ['propext','Classical.choice','Quot.sound'].includes(name)));
});
