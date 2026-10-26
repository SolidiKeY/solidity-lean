'use strict';
const test = require('node:test');
const assert = require('node:assert/strict');
const { mkdtempSync, mkdirSync, writeFileSync, readFileSync, existsSync, rmSync } = require('node:fs');
const { tmpdir } = require('node:os');
const { join } = require('node:path');
const { runBackend, parseReport } = require('../src/backend.cjs');
function fixture(t, body) {
  const root = mkdtempSync(join(tmpdir(), 'solidity-backend-'));
  mkdirSync(join(root, 'scripts'));
  writeFileSync(join(root, 'scripts/test-solidity.mjs'), body);
  t.after(() => rmSync(root, { recursive: true, force: true }));
  return root;
}
const row = { source: '/tmp/source.sol', contract: 'C', function: 'f', status: 'proved' };

test('validates report structure and preserves pending as incomplete', () => {
  assert.deepEqual(parseReport(JSON.stringify({ results: [row], errors: [] })).results, [row]);
  for (const invalid of ['not json', 'null', '{}', JSON.stringify({ results: [{ ...row, status: 'counterexample' }], errors: [] }), JSON.stringify({ results: [], errors: [null] })]) assert.throws(() => parseReport(invalid), /invalid/);
});
test('launches backend without shell and accepts unsuccessful verification report', async t => {
  const root = fixture(t, `import {writeSync} from 'node:fs';writeSync(1,JSON.stringify({results:[${JSON.stringify({ ...row, status: 'pending' })}],errors:[],args:process.argv.slice(2)}));process.exitCode=1;`);
  const report = await runBackend({ backendPath: root, nodePath: process.execPath, source: '/tmp/source with space;echo unsafe.sol', listing: true, contract: 'C', function: 'f(uint256)' });
  assert.equal(report.results[0].status, 'pending');
  assert.deepEqual(report.args.slice(-6), ['--list', '--contract', 'C', '--function', 'f(uint256)', '/tmp/source with space;echo unsafe.sol']);
});
test('reports missing backend, executable and crash distinctly', async t => {
  await assert.rejects(runBackend({ backendPath: '/missing-root', source: '/tmp/x.sol' }), /backend not found/);
  const root = fixture(t, "import {writeSync} from 'node:fs';writeSync(2,'bad compiler');process.exit(2)");
  await assert.rejects(runBackend({ backendPath: root, nodePath: '/missing-node', source: '/tmp/x.sol' }), /ENOENT/);
  await assert.rejects(runBackend({ backendPath: root, nodePath: process.execPath, source: '/tmp/x.sol' }), /exited 2: bad compiler/);
});
test('rejects invalid output and bounds overall execution', async t => {
  const root = fixture(t, "import {writeSync} from 'node:fs';writeSync(1,'garbled')");
  await assert.rejects(runBackend({ backendPath: root, nodePath: process.execPath, source: '/tmp/x.sol' }), /invalid JSON/);
  writeFileSync(join(root, 'scripts/test-solidity.mjs'), 'setInterval(()=>{},1000)');
  await assert.rejects(runBackend({ backendPath: root, nodePath: process.execPath, source: '/tmp/x.sol', timeoutMs: 100 }), error => error.code === 'TIMEOUT');
});
test('cancellation kills detached backend descendants', { skip: process.platform === 'win32' }, async t => {
  const root = fixture(t, `import {spawn} from 'node:child_process';import {writeFileSync} from 'node:fs';const child=spawn(process.execPath,['-e','setInterval(()=>{},1000)'],{detached:true,stdio:'ignore'});writeFileSync('child.pid',String(child.pid));setInterval(()=>{},1000);`);
  const abort = new AbortController();
  const result = runBackend({ backendPath: root, nodePath: process.execPath, source: '/tmp/x.sol', signal: abort.signal });
  let pid;
  for (let i = 0; i < 100; i++) {
    if (existsSync(join(root, 'child.pid'))) { pid = Number(readFileSync(join(root, 'child.pid'), 'utf8')); break; }
    await new Promise(resolve => setTimeout(resolve, 10));
  }
  assert.ok(pid, 'backend must start its detached child');
  t.after(() => { try { process.kill(pid, 'SIGKILL'); } catch {} });
  abort.abort();
  await assert.rejects(result, error => error.code === 'CANCELLED');
  for (let i = 0; i < 100; i++) {
    try {
      const state = readFileSync(`/proc/${pid}/stat`, 'utf8').split(' ')[2];
      if (state === 'Z') return; // Dead, awaiting adoption/reaping in the container.
    } catch (error) { if (error.code === 'ENOENT') return; }
    await new Promise(resolve => setTimeout(resolve, 10));
  }
  assert.fail('detached child survived cancellation');
});
test('already cancelled jobs never spawn', async t => {
  const root = fixture(t, "throw new Error('must not spawn')");
  const abort = new AbortController(); abort.abort();
  await assert.rejects(runBackend({ backendPath: root, nodePath: process.execPath, source: '/tmp/x.sol', signal: abort.signal }), error => error.code === 'CANCELLED');
});
