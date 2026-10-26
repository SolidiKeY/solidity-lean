import { test } from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { runSolidityTests } from './test-solidity.mjs';

test('declaration metadata proves canonical values and keeps a false property open', () => {
  const report = runSolidityTests(['tests/solc/DeclarationMetadata.sol'],
    { build: false, contract: 'DeclarationMetadata' });
  assert.deepEqual(report.errors, []);
  assert.equal(report.results.length, 15);
  for (const row of report.results)
    assert.equal(row.status, row.function === 'falseMetadata' ? 'pending' :
      row.function === 'receiver' ? 'internal' : 'proved',
      `${row.function}: ${row.reason}`);
  const overloads = report.results.filter(row => row.function === 'overloaded');
  assert.equal(overloads.length, 2);
  assert.deepEqual(new Set(overloads.map(row => row.signature)),
    new Set(['overloaded(uint)', 'overloaded(address)']));
  const fixture = JSON.parse(readFileSync(new URL('../tests/solc/DeclarationMetadata.ast.json', import.meta.url)));
  const contract = fixture.ast.nodes.find(node => node.name === 'DeclarationMetadata');
  const callback = contract.nodes.find(node => node.name === 'callback');
  assert.ok(contract.nodes.some(node => node.name === `solcMetadataSelector${callback.id}`),
    'the freshness regression must collide with the actual selector helper prefix');
});
