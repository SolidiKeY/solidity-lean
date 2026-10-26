'use strict';
const test = require('node:test');
const assert = require('node:assert/strict');
const { createHash } = require('node:crypto');
const { createExtension } = require('../src/extension.cjs');
const model = require('../src/model.cjs');
const { mock } = require('./mock.cjs');
const token = { isCancellationRequested: false, onCancellationRequested: () => ({ dispose() {} }) };
function row(env, overrides = {}) {
  return { source: env.doc.uri.fsPath, sourceHash: createHash('sha256').update(env.doc.text).digest('hex'), contract: 'C', function: 'f', signature: 'f(uint256)', status: 'proved', range: { start: { line: 1, character: 2 }, end: { line: 2, character: 3 } }, ...overrides };
}
function setup(backend) {
  const env = mock();
  env.api = createExtension(env.vscode, env.context, backend ? args => backend(args, env) : async () => ({ results: [row(env)], errors: [] }));
  return env;
}
const settle = () => new Promise(resolve => setImmediate(resolve));

test('model distinguishes incomplete proof, import gap, runtime error and success', () => {
  assert.equal(model.resultKind({ status: 'pending' }), 'failed');
  assert.equal(model.resultKind({ status: 'unsupported' }), 'errored');
  assert.equal(model.resultKind({ status: 'proved' }), 'passed');
  assert.equal(model.resultKind({ status: 'internal' }), 'skipped');
  assert.equal(model.validRange({ start: { line: 2, character: 0 }, end: { line: 1, character: 0 } }), false);
  assert.equal(model.validRange({ start: { line: -1, character: 0 }, end: { line: 1, character: 0 } }), false);
});
test('verify command registers proof status, Test Explorer function and hover', async () => {
  const env = setup();
  await env.commands.get('solidityLean.verify')();
  const file = env.controller.items.get(env.doc.uri.toString());
  assert.equal(file.children.size, 1);
  const item = [...file.children.values()][0];
  assert.equal(item.label, 'C.f(uint256)'); assert.equal(item.description, 'proved');
  assert.deepEqual(env.diagnosticMap.get(env.doc.uri.toString()), []);
  const hover = env.events.hover.provideHover(env.doc, { line: 1, character: 5 });
  assert.match(hover.contents.value, /proved/);
  assert.equal(env.events.hover.provideHover(env.doc, { line: 0, character: 0 }), null);
});
test('pending is warning, runtime errors are errors and ready is not a proof', async () => {
  const env = setup(async (args, env) => ({ results: [row(env, { status: args.listing ? 'ready' : 'pending', reason: 'open proof goals' })], errors: [{ source: env.doc.uri.fsPath, reason: 'compiler unavailable', stage: 'compile' }] }));
  await env.api.verify(env.doc);
  const diagnostics = env.diagnosticMap.get(env.doc.uri.toString());
  assert.deepEqual(diagnostics.map(d => d.severity), [1, 0]);
  assert.match(diagnostics[0].message, /pending/);
  await env.commands.get('solidityLean.list')();
  assert.equal(env.diagnosticMap.get(env.doc.uri.toString()).length, 1);
});
test('refuses execution in untrusted workspace and unsaved virtual documents', async () => {
  let calls = 0;
  const env = setup(async () => { calls++; });
  env.vscode.workspace.isTrusted = false;
  await assert.rejects(env.api.verify(env.doc), /trusted/);
  env.vscode.workspace.isTrusted = true; env.doc.uri.scheme = 'untitled';
  await assert.rejects(env.api.verify(env.doc), /on disk/);
  assert.equal(calls, 0);
});
test('saves dirty files and passes configured executable, timeout and backend', async () => {
  let args;
  const env = setup(async (value, env) => { args = value; return { results: [row(env)], errors: [] }; });
  env.doc.isDirty = true; env.config.backendPath = '../other'; env.config.nodePath = '/custom/node'; env.config.timeoutMs = 123;
  await env.api.verify(env.doc);
  assert.equal(env.doc.isDirty, false); assert.equal(args.backendPath, '/workspace/other');
  assert.equal(args.nodePath, '/custom/node'); assert.equal(args.timeoutMs, 123);
});
test('suppresses results from modified documents', async () => {
  let finish, signal;
  const env = setup((args, env) => new Promise(resolve => { signal = args.signal; finish = () => resolve({ results: [row(env)], errors: [] }); }));
  const promise = env.api.verify(env.doc); await settle();
  env.doc.version++; env.events.change({ document: env.doc, contentChanges: [{}] });
  assert.equal(signal.aborted, true); finish(); assert.equal(await promise, null);
  assert.equal(env.diagnosticMap.size, 0); assert.equal(env.controller.items.size, 0);
});
test('rejects stale source hashes and reports for another source', async () => {
  const env = setup(async (_, env) => ({ results: [row(env, { sourceHash: '0'.repeat(64) })], errors: [] }));
  await assert.rejects(env.api.verify(env.doc), /source hash/);
  const other = setup(async (_, env) => ({ results: [row(env, { source: '/tmp/other.sol' })], errors: [] }));
  await assert.rejects(other.api.verify(other.doc), /different source/);
});
test('verify-on-save is opt-in and cancellation command aborts the job', async () => {
  let signal, finish, calls = 0;
  const env = setup((args, env) => { calls++; signal = args.signal; return new Promise(resolve => { finish = () => resolve({ results: [row(env)], errors: [] }); }); });
  env.events.save(env.doc); await settle(); assert.equal(calls, 0);
  env.config.verifyOnSave = true; env.events.save(env.doc); await settle();
  assert.equal(calls, 1); env.commands.get('solidityLean.cancel')(); assert.equal(signal.aborted, true); finish(); await settle();
  assert.equal(env.diagnosticMap.size, 0);
});
test('Test Explorer runs one exact overloaded signature and preserves sibling statuses', async () => {
  const calls = [];
  const env = setup(async (args, env) => {
    calls.push(args);
    return { results: args.function ? [row(env)] : [row(env), row(env, { function: 'g', signature: 'g()', status: 'ready' })], errors: [] };
  });
  await env.api.verify(env.doc, { listing: true });
  const file = [...env.controller.items.values()][0], item = [...file.children.values()][0];
  await env.controller.run({ include: [item] }, token);
  assert.equal(calls[1].function, 'f(uint256)'); assert.equal(calls[1].contract, 'C');
  assert.deepEqual(env.runs[0].calls.map(call => call[0]), ['started', 'passed', 'end']);
  assert.equal(file.children.size, 2);
});
test('Test Explorer respects exclusions and maps pending without counterexample claims', async () => {
  const env = setup(async (_, env) => ({ results: [row(env, { status: 'pending', reason: 'open proof goals' })], errors: [] }));
  await env.api.verify(env.doc, { listing: true });
  const file = [...env.controller.items.values()][0], item = [...file.children.values()][0];
  await env.controller.run({ include: [file], exclude: [item] }, token);
  assert.deepEqual(env.runs[0].calls.map(call => call[0]), ['end']);
  await env.controller.run({ include: [item] }, token);
  assert.deepEqual(env.runs[1].calls.map(call => call[0]), ['started', 'failed', 'end']);
  assert.doesNotMatch(env.runs[1].calls[1][2].message, /counterexample/i);
});

test('suppresses closed documents and superseded jobs even when backend ignores cancellation', async () => {
  const pending = [];
  const env = setup((args, env) => new Promise(resolve => pending.push({ args, finish: () => resolve({ results: [row(env)], errors: [] }) })));
  const first = env.api.verify(env.doc); await settle();
  const second = env.api.verify(env.doc); await settle();
  assert.equal(pending[0].args.signal.aborted, true);
  pending[0].finish(); assert.equal(await first, null);
  env.doc.isClosed = true;
  pending[1].finish(); assert.equal(await second, null);
  assert.equal(env.reports?.size || env.api.reports.size, 0);
});
