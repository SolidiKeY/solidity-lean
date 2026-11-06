import { test } from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { mkdtempSync, mkdirSync, writeFileSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { sourceErrors, auditCommand, productionPackages, touchedProduction, buildProduction, serialConfig, headerImports, validateProductionInventory, validatePrerequisites } from './check-meaning.mjs';

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


test('production build inventory and touched closure include separate libraries and Bridge', () => {
  const dir = mkdtempSync(join(tmpdir(), 'h64-closure-'));
  try {
    const files = ['Solidity/Core.lean', 'Solidity/Corpus/Basic.lean', 'Solidity/Corpus/Other.lean',
      'Bridge/SolidityBridge/Use.lean', 'Bridge/SolidityVelvet/Use.lean',
      'Solidity/Scratch/Ignore.lean', 'tests/Ignore.lean', 'SolidityCorpus.lean'];
    for (const file of files) {
      mkdirSync(join(dir, file, '..'), { recursive: true });
      writeFileSync(join(dir, file), file.includes('Basic') ? 'import Solidity.Core\n' :
        file.includes('Bridge/Use') ? 'import Solidity.Corpus.Basic\n' :
        file.includes('Velvet/Use') ? 'public meta import\nall SolidityBridge.Use\n' :
        file === 'SolidityCorpus.lean' ? 'import Solidity.Corpus.Basic\nimport Solidity.Corpus.Other\n' : '-- leaf\n');
    }
    const packages = productionPackages(dir, files);
    assert.deepEqual(packages.map(([, ms]) => ms.length), [3, 2]);
    assert.deepEqual([...touchedProduction(dir, files, new Set(['Solidity/Core.lean']))].sort(),
      ['Solidity.Core', 'Solidity.Corpus.Basic', 'SolidityBridge.Use', 'SolidityVelvet.Use']);
    assert.equal(touchedProduction(dir, files, new Set(['docs/Change.md'])).size, 0);
    assert.deepEqual([...touchedProduction(dir, files, new Set(['Bridge/SolidityBridge/Use.lean']))].sort(),
      ['Solidity.Core', 'Solidity.Corpus.Basic', 'SolidityBridge.Use', 'SolidityVelvet.Use']);
    assert.deepEqual(headerImports('module\npublic import all\nFoo.Bar\nmeta import Qux\nopen Namespace'), ['Foo.Bar', 'Qux']);
    writeFileSync(join(dir, 'SolidityCorpus.lean'), 'import Solidity.Corpus.Basic\n');
    writeFileSync(join(dir, 'Solidity/Corpus/Other.lean'), 'import SolidityCorpus\n');
    assert.ok(touchedProduction(dir, files, new Set(['Solidity/Core.lean'])).has('Solidity.Corpus.Other'));
    assert.ok(touchedProduction(dir, files, new Set(['SolidityCorpus.lean'])).has('Solidity.Corpus.Other'));
  } finally { rmSync(dir, { recursive: true, force: true }); }
});

test('preparation rebuilds a stale audited olean, leaves unrelated targets stale and fails on build errors', () => {
  const dir = mkdtempSync(join(tmpdir(), 'h64-prepare-'));
  try {
    mkdirSync(join(dir, 'Solidity'));
    writeFileSync(join(dir, 'lean-toolchain'), 'leanprover/lean4:v4.24.0\n');
    const config = 'name = "h64-prepare"\nenableArtifactCache = false\n[[lean_lib]]\nname = "Solidity"\nweakLeanArgs = ["--tstack=131072"]\n';
    writeFileSync(join(dir, 'lakefile.toml'), config);
    for (const name of ['Wanted', 'Unrelated']) writeFileSync(join(dir, 'Solidity', name + '.lean'), 'theorem good : True := True.intro\n');
    const run = (cwd, args) => {
      const r = spawnSync('lake', args, { cwd, encoding: 'utf8', env: { ...process.env, LEAN_NUM_THREADS: '1' } });
      if (r.status) console.log(r.stdout + r.stderr);
      return r.status;
    };
    assert.equal(buildProduction(dir, ['Solidity.Wanted', 'Solidity.Unrelated'], run), 0);
    for (const name of ['Wanted', 'Unrelated']) writeFileSync(join(dir, 'Solidity', name + '.lean'), 'theorem changed : True := True.intro\n');
    assert.equal(buildProduction(dir, ['Solidity.Wanted'], run), 0);
    assert.equal(run(dir, ['--rehash', '--no-build', 'build', '+Solidity.Wanted:olean']), 0);
    assert.notEqual(run(dir, ['--rehash', '--no-build', 'build', '+Solidity.Unrelated:olean']), 0);
    writeFileSync(join(dir, 'Solidity/Wanted.lean'), 'import Solidity.Unrelated\n theorem dependent : True := True.intro\n');
    const commands = [];
    assert.notEqual(buildProduction(dir, ['Solidity.Wanted'], (cwd, args) => {
      commands.push(args);
      return run(cwd, args);
    }), 0);
    assert.equal(commands.length, 1);
    assert.ok(commands[0].includes('--no-build'));
    writeFileSync(join(dir, 'Solidity/Wanted.lean'), 'theorem broken : False := True.intro\n');
    assert.notEqual(buildProduction(dir, ['Solidity.Wanted'], run), 0);
    assert.equal(serialConfig(config).includes('"-j1"'), true);
  } finally { rmSync(dir, { recursive: true, force: true }); }
});


test('import headers stop at arbitrary commands and ignore docstrings, comments and strings', () => {
  for (const comment of [
    '/-! A docstring mentioning import foo and `close_rw_s`. -/',
    '/-- A docstring mentioning import foo and `close_rw_s`. -/',
    '/- Nested /- import foo -/ `close_rw_s` -/',
    '-- import foo `close_rw_s`',
  ]) {
    assert.deepEqual(headerImports(`import Solidity.Update\n${comment}\nregister_simp_attr close_rw_s\n`), ['Solidity.Update']);
    assert.deepEqual(headerImports(`${comment}\nimport Solidity.Update\n`), ['Solidity.Update']);
  }
  assert.deepEqual(headerImports('import Lean\ndef text := "import foo `close_rw_s`"\nimport Hidden'), ['Lean']);
  assert.deepEqual(headerImports('import Lean\n#eval s!"import foo {0}"'), ['Lean']);
  assert.deepEqual(headerImports('import Lean\n#eval r#"import foo"#'), ['Lean']);
  assert.deepEqual(headerImports('import /- comment -/ Lean\nimport\n Std\ncustom_command close_rw_s'), ['Lean', 'Std']);
  assert.deepEqual(headerImports('import Lean register_simp_attr close_rw_s'), ['Lean']);
});

test('production inventory rejects non-files and unknown library roots before Lake runs', () => {
  const dir = mkdtempSync(join(tmpdir(), 'h64-inventory-'));
  try {
    mkdirSync(join(dir, 'Solidity'));
    mkdirSync(join(dir, 'Bridge/SolidityBridge'), { recursive: true });
    writeFileSync(join(dir, 'lakefile.toml'), 'name = "fixture"\n[[lean_lib]]\nname = "Solidity"\n');
    writeFileSync(join(dir, 'Bridge/lakefile.toml'), 'name = "bridge"\n[[lean_lib]]\nname = "SolidityBridge"\n');
    writeFileSync(join(dir, 'Solidity/Real.lean'), 'import Lean\n/-! import foo `close_rw_s` -/\ntheorem good : True := True.intro');
    writeFileSync(join(dir, 'Bridge/SolidityBridge/Real.lean'), 'import Solidity.Real');
    const packages = productionPackages(dir, ['Solidity/Real.lean', 'Solidity/Fake.txt', 'Bridge/SolidityBridge/Real.lean', 'Bridge/SolidityBridge/Fake.md']);
    assert.equal(validateProductionInventory(packages), 2);
    assert.throws(() => validateProductionInventory([[dir, ['Solidity.Missing']]]), /no module file/);
    assert.throws(() => validateProductionInventory([[dir, ['Unregistered.Real']]]), /no library owns/);
    let calls = 0;
    assert.throws(() => buildProduction(dir, ['Solidity.Missing'], () => { calls++; return 0; }), /no module file/);
    assert.equal(calls, 0);
  } finally { rmSync(dir, { recursive: true, force: true }); }
});


test('foreign prerequisite preflight rejects missing modules and resolves manifest srcDir', () => {
  const dir = mkdtempSync(join(tmpdir(), 'h64-prerequisites-'));
  try {
    mkdirSync(join(dir, 'Solidity'));
    mkdirSync(join(dir, 'dep/src/Foreign'), { recursive: true });
    writeFileSync(join(dir, 'lakefile.toml'), 'name = "fixture"\n[[lean_lib]]\nname = "Solidity"\n');
    writeFileSync(join(dir, 'lake-manifest.json'), JSON.stringify({ packages: [{ type: 'path', dir: 'dep' }] }));
    writeFileSync(join(dir, 'dep/lakefile.toml'), 'name = "dep"\n[[lean_lib]]\nname = "Foreign"\nsrcDir = "src"\n');
    writeFileSync(join(dir, 'dep/src/Foreign/Real.lean'), '-- prerequisite');
    validatePrerequisites(dir, ['Foreign.Real']);
    assert.throws(() => validatePrerequisites(dir, ['Foreign.Missing']), /no module file/);
    writeFileSync(join(dir, 'Solidity/Use.lean'), 'import Foreign.Missing\n');
    let calls = 0;
    assert.throws(() => buildProduction(dir, ['Solidity.Use'], () => { calls++; return 0; }), /no module file/);
    assert.equal(calls, 0);
    writeFileSync(join(dir, 'Solidity/Use.lean'), 'import Foreign.Real\n');
    assert.equal(buildProduction(dir, ['Solidity.Use'], () => { calls++; return 0; }), 0);
    assert.equal(calls, 2);
  } finally { rmSync(dir, { recursive: true, force: true }); }
});
