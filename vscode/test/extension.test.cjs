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

test('impossible preconditions remain visible even when the postcondition is proved', async () => {
  let options;
  const env = setup(async (args, env) => {
    options = args;
    return {results:[row(env,{preconditions:'impossible',preconditionReason:'kernel-checked'})],errors:[]};
  });
  env.config.auditPreconditions = true;
  await env.api.verify(env.doc);
  assert.equal(options.auditPreconditions, true);
  const diagnostics = env.diagnosticMap.get(env.doc.uri.toString());
  assert.equal(diagnostics.length, 1);
  assert.equal(diagnostics[0].severity, 1);
  assert.equal(diagnostics[0].code, 'preconditions-impossible');
  assert.match(diagnostics[0].message, /vacuous/);
  const file = [...env.controller.items.values()][0];
  assert.match([...file.children.values()][0].description, /vacuous/);
  await env.controller.run({include:[file]}, token);
  assert.deepEqual(env.runs[0].calls.map(call => call[0]), ['started','errored','end']);
});

test('unknown audits require attention while possible entry states preserve a pass', () => {
  const base = {contract:'C',function:'f',status:'proved'};
  assert.equal(model.resultKind({...base,preconditions:'unknown'}), 'errored');
  assert.equal(model.resultKind({...base,preconditions:'notRun'}), 'errored');
  assert.equal(model.resultKind({...base,preconditions:'possible'}), 'passed');
  const unknown = model.diagnostics({results:[{...base,preconditions:'unknown',preconditionReason:'budget'}],errors:[]});
  assert.equal(unknown[0].code, 'preconditions-unknown');
  assert.doesNotMatch(unknown[0].message, /counterexample|impossible|vacuous/);
  assert.deepEqual(model.diagnostics({results:[{...base,preconditions:'possible'}],errors:[]}), []);
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
test('function hover takes precedence over a synthesized constructor spanning the contract', async () => {
  const env = setup(async (_, env) => ({results:[
    row(env,{sourceId:-1,function:'constructor',signature:'constructor()',range:{start:{line:0,character:0},end:{line:10,character:0}}}),
    row(env,{sourceId:7,status:'pending',reason:'function-specific open goals'}),
  ],errors:[]}));
  await env.api.verify(env.doc);
  assert.match(env.events.hover.provideHover(env.doc,{line:1,character:5}).contents.value,/function-specific open goals/);
  assert.match(env.events.hover.provideHover(env.doc,{line:0,character:0}).contents.value,/constructor/);
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

test('Test Explorer runs each child once when result publication replaces children', async () => {
  const calls = [];
  const env = setup(async (args, env) => {
    calls.push(args.function || 'list');
    assert.ok(calls.length <= 3, 'a file run must not restart after publication');
    const rows = [row(env), row(env, {function:'g',signature:'g()'})];
    return {results:args.function ? rows.filter(row => row.signature === args.function) : rows, errors:[]};
  });
  await env.api.verify(env.doc, {listing:true});
  const file = [...env.controller.items.values()][0];
  await env.controller.run({include:[file]}, token);
  assert.deepEqual(calls, ['list','f(uint256)','g()']);
  assert.deepEqual(env.runs[0].calls.map(call => call[0]), ['started','passed','started','passed','end']);
});

test('source hashes accept the BOM hidden by the editor without accepting other text', async () => {
  const env = setup(async (_, env) => ({results:[row(env, {
    sourceHash:createHash('sha256').update('\uFEFF' + env.doc.text).digest('hex'),
  })], errors:[]}));
  await env.api.verify(env.doc);
  assert.equal(env.api.reports.size, 1);
});

test('workspace discovery has no silent file cap and cancellation stops queued files', async () => {
  let calls = 0, finish, globArgs;
  const env = setup((args, env) => {
    calls++;
    return new Promise(resolve => { finish = () => resolve({results:[row(env)], errors:[]}); });
  });
  env.vscode.workspace.findFiles = async (...args) => { globArgs = args; return [env.doc.uri, env.doc.uri]; };
  const discovery = env.controller.resolveHandler();
  await settle();
  assert.equal(globArgs.length, 2, 'discovery must not silently omit files after a fixed cap');
  assert.equal(calls, 1);
  env.commands.get('solidityLean.cancel')();
  finish();
  await discovery;
  assert.equal(calls, 1, 'cancellation must stop the workspace queue');
});

test('cancellation during document opening cannot start a delayed discovery job', async () => {
  let calls = 0, finishOpen;
  const env = setup(async (_, env) => { calls++; return {results:[row(env)], errors:[]}; });
  env.vscode.workspace.openTextDocument = () => new Promise(resolve => { finishOpen = () => resolve(env.doc); });
  const discovery = env.controller.resolveHandler();
  await settle();
  env.commands.get('solidityLean.cancel')();
  finishOpen();
  await discovery;
  assert.equal(calls, 0);
});

test('cancellation during save cannot start a delayed verification job', async () => {
  let calls = 0, finishSave;
  const env = setup(async (_, env) => { calls++; return {results:[row(env)], errors:[]}; });
  env.doc.isDirty = true;
  env.doc.save = () => new Promise(resolve => { finishSave = () => { env.doc.isDirty = false; resolve(true); }; });
  const verification = env.api.verify(env.doc);
  await settle();
  env.commands.get('solidityLean.cancel')();
  finishSave();
  assert.equal(await verification, null);
  assert.equal(calls, 0);
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

test('certified model prestates are opt-in and appear in hover, output and failed Test Explorer results', async () => {
  const { evidence } = require('./witness.cjs');
  const calls = [];
  const witness = evidence({ lines: ['[run](command:evil)', '\u001b[31munsafe'] });
  const env = setup(async (args, env) => {
    calls.push(args);
    return { results: [row(env, { status: 'refuted', counterexample: witness })], errors: [] };
  });
  env.config.counterexamples = true;
  await env.api.verify(env.doc);
  assert.equal(calls[0].counterexamples, true);
  const diagnostic = env.diagnosticMap.get(env.doc.uri.toString())[0];
  assert.equal(diagnostic.severity, 0); assert.equal(diagnostic.code, 'refuted');
  assert.match(diagnostic.message, /certified model prestate/);
  assert.ok(env.logs.some(line => line.includes(witness.arguments[0].value)));
  const hover = env.events.hover.provideHover(env.doc, { line: 1, character: 5 });
  assert.match(hover.contents.value, /certified model prestate/);
  assert.match(hover.contents.value, /\\u001b/);
  const item = [...[...env.controller.items.values()][0].children.values()][0];
  await env.controller.run({ include: [item] }, token);
  assert.deepEqual(env.runs[0].calls.map(call => call[0]), ['started', 'failed', 'end']);
  assert.match(env.runs[0].calls[1][2].message, /certified model prestate/);
  assert.doesNotMatch(env.runs[0].calls[1][2].message, /exploit|constructor-reachable/);
  env.doc.version++; env.events.change({ document: env.doc, contentChanges: [{}] });
  assert.equal(env.api.reports.size, 0);
  assert.equal(env.events.hover.provideHover(env.doc, { line: 1, character: 5 }), null);
  assert.equal(env.controller.items.size, 0);
});
test('rejects malformed witness evidence before publishing and retains default-off option', async () => {
  let option;
  const env = setup(async (args, env) => { option = args.counterexamples; return { results: [row(env, { status: 'refuted', counterexample: { certified: true } })], errors: [] }; });
  await assert.rejects(env.api.verify(env.doc), /invalid certified model prestate/);
  assert.equal(option, false);
  assert.equal(env.api.reports.size, 0);
});
test('late witness results cannot survive cancellation, version changes or source hash mismatch', async () => {
  const { evidence } = require('./witness.cjs');
  const jobs = [];
  const env = setup((args, env) => new Promise(resolve => {
    const captured = row(env, { status: 'refuted', counterexample: evidence() });
    jobs.push({ args, finish: () => resolve({ results: [captured], errors: [] }) });
  }));
  const cancelled = env.api.verify(env.doc); await settle();
  env.api.cancel(); jobs[0].finish(); assert.equal(await cancelled, null);
  const edited = env.api.verify(env.doc); await settle();
  env.doc.version++; env.events.change({ document: env.doc, contentChanges: [{}] });
  jobs[1].finish(); assert.equal(await edited, null);
  const stale = setup(async (_, env) => ({ results: [row(env, { status: 'refuted', sourceHash: '0'.repeat(64), counterexample: evidence() })], errors: [] }));
  await assert.rejects(stale.api.verify(stale.doc), /source hash/);
  assert.equal(env.api.reports.size, 0); assert.equal(stale.api.reports.size, 0);
});

test('refuses unsolicited witness results when search is disabled or listing', async () => {
  const { evidence } = require('./witness.cjs');
  const env = setup(async (_, env) => ({ results: [row(env, {status:'refuted',counterexample:evidence()})], errors: [] }));
  await assert.rejects(env.api.verify(env.doc), /unrequested certified model prestate/);
  env.config.counterexamples = true;
  await assert.rejects(env.api.verify(env.doc, {listing:true}), /unrequested certified model prestate/);
  assert.equal(env.api.reports.size, 0);
});
