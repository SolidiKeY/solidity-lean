// Guard against confusing unavailable bodies with empty bodies or joining overloads by name.
import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import {fileURLToPath} from 'node:url';
import {spawnSync} from 'node:child_process';
import {functionSize} from './sizes.mjs';
const bytes = Buffer.from(' '.repeat(100));
const ast = bodies => ({src: '0:100:0', nodes: [{nodeType: 'ContractDefinition', name: 'C', id: 1,
  src: '0:100:0', nodes: bodies.map((body, i) => ({nodeType: 'FunctionDefinition', name: 'f',
    id: i + 2, src: '10:20:0', body}))}]});
const row = id => ({contract: 'C', function: 'f', sourceId: id});

test('empty body is zero; abstract and unknown declarations are unavailable', () => {
  const tree = ast([{nodeType: 'Block', statements: []}, null]);
  assert.equal(functionSize(tree, bytes, row(2)).statements, 0);
  assert.equal(functionSize(tree, bytes, row(3)).statements, null);
  assert.equal(functionSize(tree, bytes, row(99)).statements, null);
});

test('overloads join by declaration ID; blocks are containers and loop header statements count', () => {
  const body = {nodeType: 'Block', src: '12:5:0', statements: [{nodeType: 'ForStatement',
    initializationExpression: {nodeType: 'VariableDeclarationStatement'},
    loopExpression: {nodeType: 'ExpressionStatement'},
    body: {nodeType: 'UncheckedBlock', statements: [{nodeType: 'ExpressionStatement'}]}},
    {nodeType: 'Return'}]};
  const tree = ast([{nodeType: 'Block', statements: []}, body]);
  assert.equal(functionSize(tree, bytes, row(2)).statements, 0);
  assert.deepEqual(functionSize(tree, bytes, row(3)), {statements: 5, declarationSpanBytes: 20, reason: null});
});

test('inline assembly is one Solidity statement, not a Yul walk-step count', () => {
  const tree = ast([{nodeType: 'Block', statements: [{nodeType: 'InlineAssembly',
    AST: {nodeType: 'YulBlock', statements: [{nodeType: 'YulAssignment'}, {nodeType: 'YulAssignment'}]}}]}]);
  assert.equal(functionSize(tree, bytes, row(2)).statements, 1);
});


test('missing input report invalidates old success without compiling', () => {
  const directory = fs.mkdtempSync(path.join(os.tmpdir(), 'u01-size-control-'));
  try {
    const output = path.join(directory, 'sizes.json');
    fs.writeFileSync(output, JSON.stringify({sizesPassed: true}));
    const run = spawnSync(process.execPath, [fileURLToPath(new URL('./sizes.mjs', import.meta.url)),
      '--out', output, '--admission', path.join(directory, 'missing.json')], {encoding: 'utf8'});
    assert.equal(run.status, 1, run.stderr);
    const result = JSON.parse(fs.readFileSync(output, 'utf8'));
    assert.equal(result.sizesPassed, false);
    assert.equal(result.attemptFinished, true);
    assert.equal(result.verification, 'not-run');
    assert.ok(result.errors.length > 0);
  } finally { fs.rmSync(directory, {recursive: true, force: true}); }
});

test('input admission report cannot be overwritten by the output', () => {
  const directory = fs.mkdtempSync(path.join(os.tmpdir(), 'u01-size-control-'));
  try {
    const input = path.join(directory, 'input.json');
    const content = JSON.stringify({kind: 'u01-admission-only'});
    fs.writeFileSync(input, content);
    const run = spawnSync(process.execPath, [fileURLToPath(new URL('./sizes.mjs', import.meta.url)),
      '--out', input, '--admission', input], {encoding: 'utf8'});
    assert.equal(run.status, 2, run.stderr);
    assert.equal(fs.readFileSync(input, 'utf8'), content);
  } finally { fs.rmSync(directory, {recursive: true, force: true}); }
});


test('recorded source files and symlink aliases cannot become size-report outputs', () => {
  const directory = fs.mkdtempSync(path.join(os.tmpdir(), 'u01-size-control-'));
  try {
    const real = path.join(directory, 'real'); fs.mkdirSync(real);
    const alias = path.join(directory, 'alias'); fs.symlinkSync(real, alias, 'dir');
    const source = path.join(real, 'source.json');
    const content = 'contract C {}'; fs.writeFileSync(source, content);
    const admission = path.join(real, 'admission.json');
    fs.writeFileSync(admission, JSON.stringify({inputs: [{path: source}]}));
    for (const output of [source, path.join(alias, 'source.json'), path.join(alias, 'admission.json')]) {
      const run = spawnSync(process.execPath, [fileURLToPath(new URL('./sizes.mjs', import.meta.url)),
        '--admission', admission, '--out', output], {encoding: 'utf8'});
      assert.equal(run.status, 2, run.stderr);
      assert.equal(fs.readFileSync(source, 'utf8'), content);
      assert.deepEqual(JSON.parse(fs.readFileSync(admission, 'utf8')), {inputs: [{path: source}]});
    }
  } finally { fs.rmSync(directory, {recursive: true, force: true}); }
});
