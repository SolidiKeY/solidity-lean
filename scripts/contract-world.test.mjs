// Fixture provenance and hash rewriting for the strict world frontend.
// All generated files are temporary; this test never invokes Lean.
import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, readFileSync, writeFileSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve, dirname } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { createHash } from 'node:crypto';

const root = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const solkey = process.env.SOLKEY_ROOT || resolve(root, '../solkey');
const helper = join(root, 'scripts/solc-ast.mjs');
const source = join(root, 'tests/solc/ContractWorld.sol');
const hashOf = bytes => {
  let h = 0xcbf29ce484222325n;
  for (const b of bytes) h = ((h ^ BigInt(b)) * 0x100000001b3n) & 0xffffffffffffffffn;
  return `0x${h.toString(16).padStart(16, '0')}`;
};

test('world metadata is opt-in, deterministic, and updates every world command', async () => {
  const temp = mkdtempSync(join(tmpdir(), 'contract-world-fixture-'));
  const originalArgs = process.argv;
  let pass = 0;
  const generate = async args => {
    process.argv = [process.execPath, helper, ...args];
    await import(`${pathToFileURL(helper).href}?worldRegression=${pass++}`);
  };
  try {
    const out = join(temp, 'ContractWorld.ast.json');
    const wrapper = join(temp, 'Source.lean');
    writeFileSync(wrapper, [
      'solc_import "ContractWorld.ast.json" hash 0x1 as First',
      'solc_import "ContractWorld.ast.json" hash 0x2 as IntentionallyStale',
      'solc_world_factory "ContractWorld.ast.json" hash 0x3 contract "WorldFactory" function "make" as New',
      'solc_world_factory "ContractWorld.ast.json" hash 0x4 contract "WorldFactory" function "tryMake" as Tried',
      'solc_world_library "ContractWorld.ast.json" hash 0x5 contract "WorldLibraryUser" function "mutate" as Linked',
      'solc_world_factory "Other.ast.json" hash 0x6 contract "Other" function "make" as Other',
    ].join('\n') + '\n');
    const args = ['--solkey', solkey, '--source', source, '--out', out, '--wrapper', wrapper];
    await generate([...args, '--world-metadata']);
    const bytes = readFileSync(out), fixture = JSON.parse(bytes);
    const hash = hashOf(bytes), rewritten = readFileSync(wrapper, 'utf8');
    assert.equal(fixture.header.sourceSha256,
      createHash('sha256').update(readFileSync(source)).digest('hex'));
    assert.equal(fixture.header.provenanceVersion, 1);
    const contracts = fixture.ast.nodes.filter(n => n.nodeType === 'ContractDefinition');
    assert(contracts.length > 0 && contracts.every(n => n.abstract === false));
    assert.equal((rewritten.match(new RegExp(`hash ${hash}`, 'g')) || []).length, 4);
    assert(rewritten.includes('hash 0x2 as IntentionallyStale'));
    assert(rewritten.includes('"Other.ast.json" hash 0x6'));
    await generate([...args, '--world-metadata']);
    assert.deepEqual(readFileSync(out), bytes);
    await generate([...args, '--no-wrapper']);
    const ordinary = JSON.parse(readFileSync(out));
    assert(ordinary.ast.nodes.filter(n => n.nodeType === 'ContractDefinition')
      .every(n => !Object.hasOwn(n, 'abstract')));
  } finally {
    process.argv = originalArgs;
    rmSync(temp, { recursive: true, force: true });
  }
});
