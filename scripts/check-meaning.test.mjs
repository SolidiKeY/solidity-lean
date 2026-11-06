import { test } from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { mkdtempSync, mkdirSync, writeFileSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { sourceErrors, auditCommand } from './check-meaning.mjs';

test('planted source escapes fail, including quoted macros and attributes', () => {
  for (const src of [
    'theorem planted : True := by sorry', 'theorem planted : True := by admit',
    'theorem planted : True := by native_decide', 'by decide +native',
    'set_option debug.skipKernelTC true', 'set_option test.skipKernelAnything true',
    'set_option Elab.async true', 'set_option Elab.«async» true',
    'set_option Elab /- comment -/ . async true',
    '@[implemented_by bypass] def f : Nat := 0', 'withOptions (Elab.async.set · true) action',
    'macro "evil" : tactic => `(tactic| sorry)',
    'macro "evil" : command => `(set_option debug.skipKernelTC true)',
    '@[my_attr (by native_decide)] theorem planted : True := by trivial',
    'axiom planted : False',
  ]) assert.ok(sourceErrors('Solidity/Plant.lean', src, '').length, src);
  assert.deepEqual(sourceErrors('X.lean', '/- sorry /- admit -/ -/\n-- native_decide', ''), []);
  assert.deepEqual(sourceErrors('X.lean', 'set_option Elab.async false', ''), []);
});

test('exceptions are path-local counted sites; proof holes cannot be grandfathered', () => {
  const src = 'withOptions (debug.skipKernelTC.set · true) action';
  assert.deepEqual(sourceErrors('X.lean', src, src), []);
  assert.ok(sourceErrors('X.lean', src + '\n' + src, src).length);
  assert.ok(sourceErrors('X.lean', 'by sorry', 'by sorry').length);
  assert.ok(sourceErrors('X.lean', 'by native_decide', '').length);
});

test('live Lean dependency audit passes good proof and rejects new axiom and generated sorry', () => {
  const dir = mkdtempSync(join(tmpdir(), 'h64-selftest-'));
  const lean = execFileSync('lake', ['env', 'which', 'lean'], { encoding: 'utf8' }).trim();
  const leanPath = execFileSync('lake', ['env', 'printenv', 'LEAN_PATH'], { encoding: 'utf8' }).trim();
  const env = { ...process.env, LEAN_NUM_THREADS: '1', LEAN_PATH: dir + ':' + leanPath };
  const run = args => spawnSync(lean, ['--tstack=131072', '-j1', '--root=' + dir, ...args], { env, encoding: 'utf8' });
  try {
    mkdirSync(join(dir, 'Solidity'));
    for (const [label, body, pass, expected] of [
      ['good', 'theorem good : True := True.intro', true, 'live theorem axiom sets checked'],
      ['frozen good', 'def frozen : True := True.intro', true, 'live theorem axiom sets checked'],
      ['local generated axiom', 'theorem good : True := True.intro', false, 'hidden'],
      ['unused axiom', 'axiom planted : False\ntheorem good : True := True.intro', false, 'planted'],
      ['axiom', 'axiom planted : False\ntheorem bad : False := planted', false, 'planted'],
      ['sorry', 'macro "hiddenHole" : tactic => `(tactic| sorry)\ntheorem bad : False := by hiddenHole', false, 'sorryAx'],
      ['frozen axiom', 'axiom planted : False\ndef frozen : False := planted', false, 'planted'],
      ['native', 'theorem bad : True := by native_decide', false, 'Lean.ofReduceBool'],
    ]) {
      writeFileSync(join(dir, 'Solidity', 'H64Fixture.lean'), 'import Lean\nnamespace Solidity.H64Fixture\n' + body + '\nend Solidity.H64Fixture\n');
      const compiled = run(['-o', join(dir, 'Solidity', 'H64Fixture.olean'), join(dir, 'Solidity', 'H64Fixture.lean')]);
      assert.equal(compiled.status, 0, `${label} fixture compile: ${compiled.stdout}${compiled.stderr}`);
      const local = label === 'local generated axiom' ? 'open Lean Elab Command in\nrun_cmd do\n  addDecl <| Declaration.axiomDecl { name := `Solidity.H64Fixture.hidden, levelParams := [], type := mkConst ``False, isUnsafe := false }\n' : '';
      writeFileSync(join(dir, 'Audit.lean'), 'import Solidity.H64Fixture\n' + local + auditCommand({}, false, label.startsWith('frozen') ? ['Solidity.H64Fixture.frozen'] : []));
      const checked = run([join(dir, 'Audit.lean')]);
      assert.equal(checked.status === 0, pass, `${label}: ${checked.stdout}${checked.stderr}`);
      assert.ok((checked.stdout + checked.stderr).includes(expected), `${label}: ${checked.stdout}${checked.stderr}`);
      console.log(`${label}: ${pass ? 'PASS' : 'rejected as required'}`);
    }
  } finally { rmSync(dir, { recursive: true, force: true }); }
});

test('Lake freshness prerequisite rejects stale cached proof artifacts', () => {
  const dir = mkdtempSync(join(tmpdir(), 'h64-freshness-'));
  try {
    mkdirSync(join(dir, 'Solidity'));
    writeFileSync(join(dir, 'lean-toolchain'), 'leanprover/lean4:v4.24.0\n');
    writeFileSync(join(dir, 'lakefile.toml'), 'name = "h64-fixture"\nenableArtifactCache = false\n[[lean_lib]]\nname = "Solidity"\nweakLeanArgs = ["-j1"]\n');
    const src = join(dir, 'Solidity', 'Fresh.lean');
    writeFileSync(src, 'theorem fresh : True := True.intro\n');
    const run = args => spawnSync('lake', args, { cwd: dir, encoding: 'utf8', env: { ...process.env, LEAN_NUM_THREADS: '1' } });
    const build = run(['build', '+Solidity.Fresh:olean']);
    assert.equal(build.status, 0, build.stdout + build.stderr);
    const good = run(['--rehash', '--no-build', 'build', '+Solidity.Fresh:olean']);
    assert.equal(good.status, 0, good.stdout + good.stderr);
    writeFileSync(src, 'axiom untrusted : False\ntheorem fresh : False := untrusted\n');
    const stale = run(['--rehash', '--no-build', 'build', '+Solidity.Fresh:olean']);
    assert.notEqual(stale.status, 0, stale.stdout + stale.stderr);
    console.log('stale cached proof: rejected as required');
  } finally { rmSync(dir, { recursive: true, force: true }); }
});
