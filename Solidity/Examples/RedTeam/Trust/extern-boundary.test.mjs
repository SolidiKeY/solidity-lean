import assert from 'node:assert/strict';
import {mkdtempSync, readFileSync, writeFileSync, rmSync} from 'node:fs';
import {tmpdir} from 'node:os';
import {join} from 'node:path';
import {execFileSync} from 'node:child_process';
import {test} from 'node:test';
import {findings} from '../../../../scripts/check-trust.mjs';
import {sourceAttributes, requireLinks} from '../../../../scripts/trust/trust-implemented-by.mjs';

const module = readFileSync(new URL('./ExternBoundary.lean', import.meta.url), 'utf8');
const marker = '-- NATIVE_IMPLEMENTATION_FIXTURE';
assert.equal(module.split(marker).length, 2, 'exactly one implementation marker');
const fixture = module.replace(marker, '@[extern "lean_nat_add"]') +
  '\ndef main : IO Unit := IO.println (Solidity.Examples.RedTeam.Trust.ExternBoundary.first 0 1)\n';

test('isolated external implementation passes source lint despite native disagreement', () => {
  assert.deepEqual(findings(fixture), []);
  const dir = mkdtempSync(join(tmpdir(), 'trust-extern-'));
  try {
    writeFileSync(join(dir, 'Witness.lean'), fixture);
    const attributes = sourceAttributes(dir);
    assert.equal(attributes.filter(x => x.kind === 'extern').length, 1);
    assert.throws(() => requireLinks([{module: 'control', declaration: 'first',
      implementation: null, extern: true, links: []}]), /missing kernel equality links/);
    const env = {...process.env, LEAN_NUM_THREADS: '1'};
    execFileSync('lean', ['-j1', '-c', 'Witness.c', 'Witness.lean'], {cwd: dir, env});
    execFileSync('leanc', ['-o', 'witness', 'Witness.c'], {cwd: dir, env});
    assert.equal(execFileSync(join(dir, 'witness'), [], {encoding: 'utf8'}).trim(), '1');
  } finally {
    rmSync(dir, {recursive: true, force: true});
  }
});
