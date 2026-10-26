// Exercise fixture hash regeneration through its argument-driven entry point with a local compiler
// stub in explicit legacy-fixture mode; no Lean or compiler download is used.
import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, mkdirSync, readFileSync, writeFileSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { createHash } from 'node:crypto';

const helper = fileURLToPath(new URL('./solc-ast.mjs', import.meta.url));
const hashOf = bytes => {
  let h = 0xcbf29ce484222325n;
  for (const b of bytes) h = BigInt.asUintN(64, (h ^ BigInt(b)) * 0x100000001b3n);
  return `0x${h.toString(16).padStart(16, '0')}`;
};

let pass = 0;
async function fixtureSetup(run) {
  const originalArgs = process.argv;
  const temp = mkdtempSync(join(tmpdir(), 'solc-fixture-hashes-'));
  try {
    const solkey = join(temp, 'solkey');
    const compilerDir = join(solkey, 'keyext.solidity.core/build/soljson');
    mkdirSync(compilerDir, { recursive: true });
    const compiler = join(compilerDir, 'stub.cjs');
    const stub = `module.exports = { cwrap(name) {
      if (name === 'solidity_version') return () => 'fixture-hash-test';
      if (name === 'solidity_compile') return raw => {
        const unit = Object.keys(JSON.parse(raw).sources)[0];
        return JSON.stringify({sources:{[unit]:{ast:{nodeType:'SourceUnit',nodes:[]}}}});
      };
      throw Error(name);
    }};\n`;
    writeFileSync(compiler, stub);
    const sha = createHash('sha256').update(stub).digest('hex');
    writeFileSync(join(solkey, 'keyext.solidity.core/build.gradle'),
      `ext.soljsonFile = "stub.cjs"\next.soljsonSha256 = "${sha}"\n`);
    writeFileSync(join(solkey, 'snapshot.json'), '{"commit":"fixture-hash-test"}\n');
    const source = join(temp, 'C.sol');
    const out = join(temp, 'C.ast.json');
    const wrapper = join(temp, 'Imports.lean');
    writeFileSync(source, 'contract C {}\n');
    const generate = async (options = []) => {
      process.argv = [process.execPath, helper, '--legacy-fixture', '--solkey', solkey,
        '--source', source, '--out', out, '--wrapper', wrapper, ...options];
      await import(`${pathToFileURL(helper).href}?hashRegression=${pass++}`);
    };
    await run({temp, source, out, wrapper, generate});
  } finally {
    process.argv = originalArgs;
    rmSync(temp, { recursive: true, force: true });
  }
}

test('regeneration updates every formerly valid import while preserving stale and other fixtures', async () => {
  await fixtureSetup(async ({temp, source, out, wrapper, generate}) => {
    await generate(['--no-wrapper']);
    const oldHash = hashOf(readFileSync(out));
    mkdirSync(join(temp, 'other'));
    writeFileSync(join(temp, 'other/C.ast.json'), readFileSync(out));
    const stale = oldHash === '0x0000000000000001' ? '0x2' : '0x1';
    const worldStale = oldHash === '0x0000000000000003' ? '0x4' : '0x3';
    writeFileSync(wrapper, [
      `solc_import "C.ast.json" hash ${stale} as IntentionallyStaleFirst`,
      `solc_import "C.ast.json" hash ${oldHash} as First`,
      `solc_import "./C.ast.json" hash 0X${BigInt(oldHash).toString(16).toUpperCase()} as Second`,
      `solc_import "C.ast.json" hash ${oldHash} as Third testing`,
      `solc_world_factory "C.ast.json" hash ${oldHash} contract "C" function "make" as Factory`,
      `solc_world_library "C.ast.json" hash ${oldHash} contract "C" function "run" as Library`,
      `solc_world_factory "C.ast.json" hash ${worldStale} contract "C" function "bad" as StaleWorld`,
      `solc_import "other/C.ast.json" hash ${oldHash} as OtherDirectory`,
      `solc_import "NotC.ast.json" hash ${oldHash} as OtherBasename`,
      `-- C.ast.json has the hash ${oldHash}, not the one named`,
    ].join('\n') + '\n');
    writeFileSync(source, 'contract C { uint changed; }\n');
    await generate();
    const newHash = hashOf(readFileSync(out));
    assert.notEqual(newHash, oldHash);
    const rewritten = readFileSync(wrapper, 'utf8');
    assert.equal((rewritten.match(new RegExp(`hash ${newHash}`, 'g')) || []).length, 6);
    for (const name of ['First', 'Second', 'Third'])
      assert(rewritten.includes(`hash ${newHash} as ${name}`), name);
    assert(rewritten.includes(`hash ${stale} as IntentionallyStaleFirst`));
    assert(rewritten.includes(`hash ${worldStale} contract "C" function "bad"`));
    assert(rewritten.includes(`"other/C.ast.json" hash ${oldHash}`));
    assert(rewritten.includes(`"NotC.ast.json" hash ${oldHash}`));
    await generate();
    assert.equal(readFileSync(wrapper, 'utf8'), rewritten, 'unchanged regeneration is stable');
    writeFileSync(source, 'contract C { uint changed; uint again; }\n');
    await generate(['--no-wrapper']);
    assert.equal(readFileSync(wrapper, 'utf8'), rewritten, '--no-wrapper does not rewrite imports');
  });
});

test('initial generation retains the first-import bootstrap and stale negative imports', async () => {
  await fixtureSetup(async ({out, wrapper, generate}) => {
    writeFileSync(wrapper, [
      'solc_import "C.ast.json" hash 0x1 as First',
      'solc_import "C.ast.json" hash 0x2 as IntentionallyStale',
      'solc_world_factory "C.ast.json" hash 0x3 contract "C" function "make" as New',
      'solc_world_library "C.ast.json" hash 0x4 contract "C" function "run" as Linked',
    ].join('\n') + '\n');
    await generate();
    const hash = hashOf(readFileSync(out));
    const text = readFileSync(wrapper, 'utf8');
    assert.equal((text.match(new RegExp(`hash ${hash}`, 'g')) || []).length, 3);
    assert(text.includes('hash 0x2 as IntentionallyStale'));
  });
});
