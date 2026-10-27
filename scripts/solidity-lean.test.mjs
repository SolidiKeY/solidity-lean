import {test} from 'node:test';
import assert from 'node:assert/strict';
import {spawnSync} from 'node:child_process';
import {mkdtempSync, writeFileSync, rmSync, copyFileSync} from 'node:fs';
import {tmpdir} from 'node:os';
import {resolve, join, dirname} from 'node:path';
import {fileURLToPath} from 'node:url';
import {parseArgs, reportExitCode, VERSION} from './solidity-lean.mjs';

const ROOT = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const binary = resolve(ROOT, '.lake/build/bin/solidity-lean');
const source = resolve(ROOT, 'tests/solc/Cli.sol');

function cli(args, code = 0, cwd = ROOT) {
  const p = spawnSync(binary, [...args, '--json'], {cwd, encoding:'utf8', timeout:120000});
  assert.ifError(p.error);
  assert.equal(p.status, code, p.stdout + p.stderr);
  const report = JSON.parse(p.stdout);
  assert.equal(report.schemaVersion, 1);
  assert.equal(report.version, VERSION);
  return report;
}

test('strict parsing preserves overload signatures, exact words, and path separators', () => {
  const parsed = parseArgs(['verify', 'Token.sol', '--function', 'transfer(address,uint256)', '--timeout', '30s']);
  assert.equal(parsed.options.timeoutMs, 30000);
  assert.equal(parsed.options.function, 'transfer(address,uint256)');
  assert.deepEqual(parseArgs(['list', '--', '-source.sol']).paths, ['-source.sol']);
  assert.deepEqual(parseArgs(['list', '--', '--help']).paths, ['--help']);
  assert.deepEqual(parseArgs(['run', 'C.sol', '--function', 'f', '--arg', '-7', '--arg', 'true']).options.args, ['-7', true]);
  for (const args of [[], ['--help'], ['verify', '--help']]) assert.equal(parseArgs(args).help, true);
  for (const args of [ ['wat'], ['verify'], ['rules'], ['verify', 'x', '--show', 'tree'],
    ['verify', 'x', '--timeout', '0'], ['verify', 'x', '--timeout', '1.5s'],
    ['verify', 'x', '--timeout', '2147483648ms'], ['list', 'x', '--contract'],
    ['run', 'x'], ['inspect', 'x', '--show', 'wat'], ['rules', 'check', 'x'],
    ['verify', 'x', '--self-address', (1n << 160n).toString()],
    ['run', 'x', '--function', 'f', '--arg', '1; assert(false)'],
    ['list', 'x', '--contract', 'A', '--contract', 'B'] ]) assert.throws(() => parseArgs(args));
});

test('exit policy keeps pending proofs distinct from successful inspection', () => {
  const report = status => ({results:[{status}], errors:[]});
  assert.equal(reportExitCode('verify', report('proved')), 0);
  for (const status of ['pending', 'unsupported', 'refuted', 'error', 'skipped'])
    assert.equal(reportExitCode('verify', report(status)), 1);
  assert.equal(reportExitCode('inspect', report('pending')), 0);
  assert.equal(reportExitCode('run', report('panic')), 1);
  assert.equal(reportExitCode('inspect', {results:[], errors:[{stage:'discovery'}]}), 2);
});

test('native help, version, and invocation errors work outside the checkout', () => {
  for (const args of [['--help'], ['--version']]) {
    const p = spawnSync(binary, args, {cwd:tmpdir(), encoding:'utf8'});
    assert.equal(p.status, 0, p.stderr);
    assert.match(p.stdout, /solidity-lean/);
  }
  const report = cli(['verify', '--unknown'], 2, tmpdir());
  assert.match(report.errors[0].reason, /unknown option/);
  assert.deepEqual(report.results, []);
  cli(['verify', '/does-not-exist'], 2);
});

test('native verification retains checked positives, open goals, and import gaps', () => {
  const positive = cli(['verify', source, '--function', 'passes', '--no-build']);
  assert.equal(positive.results[0].status, 'proved');
  assert.deepEqual(positive.errors, []);
  const negative = cli(['verify', source, '--function', 'fails', '--no-build'], 1);
  assert.equal(negative.results[0].status, 'pending');
  const gap = cli(['list', source, '--function', 'forbidden', '--no-build'], 1);
  assert.equal(gap.results[0].status, 'excluded');
  const listed = cli(['list', source, '--function', 'overloaded(uint256)', '--no-build']);
  assert.equal(listed.results.length, 1);
  assert.equal(listed.results[0].signature, 'overloaded(uint)');
  assert.equal(listed.results[0].status, 'ready');
  cli(['verify', source, '--function', 'missing', '--no-build'], 2);
});

test('inspection exposes source premises, specified obligations, goals, and structured trees', () => {
  const base = ['inspect', source, '--no-build'];
  const obligation = cli([...base, '--function', 'passes']).results[0];
  assert.equal(obligation.status, 'inspected');
  assert.match(obligation.text, /\\problem/);
  assert.match(obligation.text, /160|1461501637330902918203684832716283019655932542976/);
  const clean = cli(['inspect', resolve(ROOT, 'tests/solc/CliClean.sol'), '--no-build']).results[0];
  assert.match(clean.text, /cleanTail/);
  const specified = cli([...base, '--function', 'specified']).results[0];
  assert.equal(specified.status, 'inspected');
  assert.ok(specified.text.length > 0);
  const goals = cli([...base, '--function', 'fails', '--show', 'goals']).results[0];
  assert.equal(goals.status, 'pending');
  assert.match(goals.text, /open proof goals/);
  assert.match(goals.text, /⊢/);
  const tree = cli([...base, '--function', 'passes', '--show', 'tree']).results[0];
  assert.equal(tree.status, 'inspected');
  assert.equal(tree.tree.closed, true);
  assert.ok(tree.tree.stats);
});

test('concrete calls preserve exact input, storage, overloads, and failure outcomes', () => {
  const dir = mkdtempSync(join(tmpdir(), 'solidity-cli-'));
  try {
    const state = join(dir, 'initial state.json');
    writeFileSync(state, JSON.stringify({storage:{count:'41'}, sender:'0x7', selfAddress:'0x8'}));
    const run = cli(['run', source, '--function', 'inc', '--arg', '1', '--state', state, '--no-build']).results[0];
    assert.equal(run.status, 'ok');
    assert.match(run.text, /returns 42/);
    assert.match(run.text, /count = 42/);
    const panic = cli(['run', source, '--function', 'fails', '--no-build'], 1).results[0];
    assert.equal(panic.status, 'panic');
    const word = ((1n << 256n) - 1n).toString();
    const exact = cli(['run', source, '--function', 'overloaded(uint256)', '--arg', word, '--no-build']).results[0];
    assert.ok(exact.text.includes(word));
    const boolean = cli(['run', source, '--function', 'overloaded(bool)', '--arg', 'true', '--no-build']).results[0];
    assert.match(boolean.text, /returns true/);
    cli(['run', source, '--function', 'overloaded', '--arg', '1', '--no-build'], 2);
    writeFileSync(state, '{"storage":{"count":9007199254740993}}');
    cli(['run', source, '--function', 'inc', '--state', state], 2);
    writeFileSync(state, '{"typo":"7"}');
    cli(['run', source, '--function', 'inc', '--state', state], 2);
    const spaced = join(dir, 'a contract.sol');
    copyFileSync(source, spaced);
    const outside = cli(['list', 'a contract.sol', '--function', 'passes', '--no-build'], 0, dir);
    assert.equal(outside.results[0].source, spaced);
  } finally { rmSync(dir, {recursive:true, force:true}); }
});

test('rules check requires a real file and audits the frozen upstream rules', () => {
  cli(['rules', 'check', '--key', '/does-not-exist'], 2);
  const key = resolve(ROOT, 'tests/migration/solkey/keyext.solidity.core/src/main/resources/org/key_project/solidity/proof/rules/solidityProgramRules.key');
  const report = cli(['rules', 'check', '--key', key, '--no-build']);
  assert.equal(report.results[0].status, 'matched');
  assert.deepEqual(report.errors, []);
});
