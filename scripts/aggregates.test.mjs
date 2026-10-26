import {test} from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync, writeFileSync, mkdtempSync, rmSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {tmpdir} from 'node:os';
import {join, resolve} from 'node:path';
import {runTool} from './test-solidity.mjs';

test('pinned aggregate source proves a literal property and leaves its false assertion open', () => {
  const fixture = resolve('tests/solc/Aggregates.ast.json');
  const data = readFileSync(fixture);
  const ast = JSON.parse(data);
  assert.match(ast.header.solcVersion, /^0\.8\.38/);
  assert.equal(ast.header.sourceSha256, createHash('sha256').update(readFileSync('tests/solc/Aggregates.sol')).digest('hex'));
  let hash = 14695981039346656037n;
  for (const b of data) hash = BigInt.asUintN(64, (hash ^ BigInt(b)) * 1099511628211n);
  const dir = mkdtempSync(join(tmpdir(), 'aggregate-test-'));
  try {
    const positive = join(dir, 'positive.json');
    const negative = join(dir, 'negative.json');
    const source = `import Solidity.Frontend.Testing
solc_import ${JSON.stringify(fixture)} hash 0x${hash.toString(16)} as AggregateTest.Aggregates testing
solc_scoped_problems AggregateTest.Aggregates decl
#solkey_test AggregateTest.Aggregates only "literals" to ${JSON.stringify(positive)}
#solkey_test AggregateTest.Aggregates only "falsePost" to ${JSON.stringify(negative)}
`;
    const file = join(dir, 'Test.lean');
    writeFileSync(file, source);
    runTool('lake', ['--quiet', '--no-build', 'lean', file, '--', '--tstack=131072'], 300000);
    const yes = JSON.parse(readFileSync(positive));
    const no = JSON.parse(readFileSync(negative));
    assert.equal(yes.length, 1); assert.equal(yes[0].status, 'proved');
    assert.equal(no.length, 1); assert.equal(no[0].status, 'pending');
  } finally { rmSync(dir, {recursive:true, force:true}); }
});
