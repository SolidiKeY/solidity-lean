// The site exporter against a stand-in language server, so the protocol
// handling is tested without Lean: `node --test scripts/site/export.test.mjs`.
import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { LspClient, recordFile, describe, goalPositions } from './export.mjs';

// Answers like Lean's server: diagnostics before `waitForDiagnostics`
// returns, a tactic goal on line 2, an expected type on line 1, `null`
// elsewhere, and one request of its own that the client must acknowledge.
const server = String.raw`
let buf = Buffer.alloc(0);
const send = (m) => { const b = Buffer.from(JSON.stringify(m)); process.stdout.write('Content-Length: ' + b.length + '\r\n\r\n'); process.stdout.write(b); };
process.stdin.on('data', (c) => {
  buf = Buffer.concat([buf, c]);
  for (;;) {
    const h = buf.indexOf('\r\n\r\n'); if (h < 0) return;
    const n = Number(/Content-Length: (\d+)/.exec(buf.subarray(0, h).toString())[1]);
    if (buf.length < h + 4 + n) return;
    const m = JSON.parse(buf.subarray(h + 4, h + 4 + n).toString()); buf = buf.subarray(h + 4 + n);
    if (m.method === 'initialize') { send({ jsonrpc: '2.0', id: 99, method: 'client/registerCapability', params: {} }); send({ jsonrpc: '2.0', id: m.id, result: { capabilities: {} } }); }
    else if (m.method === 'textDocument/waitForDiagnostics') {
      send({ jsonrpc: '2.0', method: 'textDocument/publishDiagnostics', params: { uri: m.params.uri, diagnostics: [
        { severity: 3, range: { start: { line: 3, character: 0 }, end: { line: 3, character: 5 } }, message: 'info: 2' },
        { severity: 1, range: { start: { line: 1, character: 0 }, end: { line: 1, character: 1 } }, fullRange: { start: { line: 1, character: 0 }, end: { line: 2, character: 4 } }, message: 'unsolved goals' } ] } });
      send({ jsonrpc: '2.0', id: m.id, result: {} });
    }
    else if (m.method === '$/lean/plainGoal') send({ jsonrpc: '2.0', id: m.id, result: m.params.position.line === 2 ? { rendered: '', goals: ['x : Nat\n⊢ x = x'] } : null });
    else if (m.method === '$/lean/plainTermGoal') {
      if (m.params.position.line === 3) send({ jsonrpc: '2.0', id: m.id, error: { code: -32801, message: 'no info' } });
      else send({ jsonrpc: '2.0', id: m.id, result: m.params.position.line === 1 ? { goal: '⊢ Prop', range: {} } : null });
    }
    else if (m.method === 'shutdown') send({ jsonrpc: '2.0', id: m.id, result: null });
    else if (m.method === 'exit') process.exit(0);
  }
});`;

test('records diagnostics and the goal at the end of each line', async () => {
  const dir = mkdtempSync(join(tmpdir(), 'site-export-'));
  const file = join(dir, 'Example.lean');
  writeFileSync(file, 'theorem t (x : Nat) :\n    x = x := by\n  rfl\n#eval 1 + 1\n');
  const client = new LspClient(process.execPath, ['-e', server], {});
  await client.request('initialize', { processId: null, rootUri: null, capabilities: {} });
  const out = await recordFile(client, file);
  assert.deepEqual(out.messages.map((m) => [m.severity, m.start.line, m.end.line]),
    [['error', 1, 2], ['information', 3, 3]]);
  assert.deepEqual(out.goals, {
    1: { kind: 'term', goals: ['⊢ Prop'] },
    2: { kind: 'tactic', goals: ['x : Nat\n⊢ x = x'] },
  });
  await client.request('shutdown', null);
  client.notify('exit', null);
  assert.equal((await client.closed).code, 0);
});

test('describes a module by its docstring heading', () => {
  assert.deepEqual(describe('/-!\n# Loops\n\nA `while` loop,\nby invariant.\n\nMore.\n-/', 'X.lean'),
    { title: 'Loops', summary: 'A `while` loop, by invariant.' });
  assert.deepEqual(describe('import A\n', 'dir/MaxElem.lean'), { title: 'MaxElem', summary: '' });
});

test('asks for goals at the last non-blank column, in UTF-16 units', () => {
  assert.deepEqual(goalPositions('a ⊢ b  \n\n  c'), [{ line: 0, character: 5 }, { line: 2, character: 3 }]);
});
