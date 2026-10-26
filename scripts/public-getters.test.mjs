import {test} from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {runSolidityTests} from './test-solidity.mjs';

const source = 'tests/solc/PublicGetters.sol';
const fixture = JSON.parse(readFileSync(new URL('../tests/solc/PublicGetters.ast.json', import.meta.url)));
const contract = name => fixture.ast.nodes.find(node => node.name === name);
const member = (owner, name) => contract(owner).nodes.find(node => node.name === name);

test('getter fixture retains compiler identities and real name collisions', () => {
  const count = member('PublicGetters', 'count');
  assert.match(count.functionSelector, /^[0-9a-f]{8}$/);
  assert.ok(count.baseFunctions.length > 0, 'public variable must override the interface declaration');
  assert.ok(member('PublicGetters', `solcGetter${count.id}`));
  const items = member('PublicGetters', 'items');
  assert.ok(member('PublicGetters', `solcGetterArg${items.id}_0`));
  const baseCtor = contract('GetterReturnBase').nodes.find(node => node.kind === 'constructor');
  assert.ok(member('GetterCtorCollision', `solcCtorBody${baseCtor.id}`));
  const mapping = member('PublicGetters', 'allowances').typeName;
  assert.equal(mapping.keyName, 'who');
  assert.equal(mapping.valueType.keyName, 'kind');
});

test('getters execute through imported self calls; a false assertion stays pending', () => {
  const report = runSolidityTests([source], {build:false, contract:'PublicGetters'});
  assert.deepEqual(report.errors, []);
  assert.equal(report.results.length, 15);
  for (const row of report.results) {
    const expected = ['falseScalar','falseBoundsPanic'].includes(row.function) ? 'pending' :
      row.function.startsWith('solcGetter') ? 'internal' : 'proved';
    assert.equal(row.status, expected, `${row.function}: ${row.reason}`);
  }
});

test('reference returns fail closed without changing struct omissions', () => {
  const report = runSolidityTests([source], {build:false, contract:'GetterReferences'});
  assert.deepEqual(report.errors, []);
  assert.equal(report.results.length, 3);
  for (const row of report.results) {
    if (row.function === 'localBytes') assert.equal(row.status, 'proved', row.reason);
    else {
      assert.equal(row.status, 'unsupported', `${row.function}: ${row.reason}`);
      assert.match(row.reason, /reference|getter/);
    }
  }
});

test('dynamic byte prefixes preserve padding, single evaluation and lazy branches', () => {
  const report = runSolidityTests([source], {build:false, contract:'GetterBytePrefixes'});
  assert.deepEqual(report.errors, []);
  const expected = ['emptyPrefix','shortPrefix','leadingZeroPrefix','longPrefix',
    'evaluateOnce','lazyPrefix'];
  assert.deepEqual(report.results.filter(row => row.status !== 'internal')
    .map(row => row.function).sort(), expected.sort());
  for (const row of report.results) {
    assert.equal(row.status, ['make','broken'].includes(row.function) ? 'internal' : 'proved',
      `${row.function}: ${row.reason}`);
  }
});

test('constructor helper collisions preserve deployment and reject a false constructor assertion', () => {
  for (const [name, expected] of [['GetterCtorCollision','proved'], ['GetterCtorFalse','pending']]) {
    const report = runSolidityTests([source], {build:false, contract:name});
    assert.deepEqual(report.errors, []);
    assert.equal(report.results.find(row => row.function === 'constructor')?.status, expected, name);
  }
});

test('printed struct aliases also reserve constructor helper names', () => {
  const baseCtor = contract('GetterReturnBase').nodes.find(node => node.kind === 'constructor');
  const report = runSolidityTests([source], {build:false, contract:'GetterCtorStructAlias',
    renaming:{GetterBox:`solcCtorBody${baseCtor.id}`}});
  assert.deepEqual(report.errors, []);
  assert.equal(report.results.find(row => row.function === 'constructor')?.status, 'proved');
});

test('a public function-valued slot is distinct from its synthesized getter selector', () => {
  const report = runSolidityTests([source], {build:false, contract:'GetterFunctionSlot'});
  assert.deepEqual(report.errors, []);
  assert.equal(report.results.find(row => row.function === 'falseStoredSelector')?.status, 'pending');
  assert.equal(report.results.find(row => row.function === 'getterSelector')?.status, 'proved');
});
