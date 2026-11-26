'use strict';
const test = require('node:test');
const assert = require('node:assert/strict');
const fs = require('node:fs');
const os = require('node:os');
const path = require('node:path');
const editor = require('../src/features/index.cjs');
const server = require('../src/server-features/index.cjs');

function fixture(t, files) {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'solidity-features-'));
  t.after(() => fs.rmSync(dir, {recursive:true, force:true}));
  for (const [name, body] of Object.entries(files)) fs.writeFileSync(path.join(dir, name), body);
  return dir;
}

test('editor loads in sorted order, isolates failures, supplies fallbacks and disposes once', t => {
  const events = [], messages = [], commands = new Map();
  const vscode = {commands:{registerCommand(name, handler) {
    assert.ok(!commands.has(name)); commands.set(name, handler);
    return {dispose() {events.push(`dispose ${name}`); commands.delete(name);}};
  }}, window:{showInformationMessage(message) {messages.push(message);}}};
  const dir = fixture(t, {
    'z.cjs': `exports.activate=(c,s)=>{s.events.push('z');c.subscriptions.push({dispose(){s.events.push('dispose z')}})}`,
    'b.cjs': `exports.activate=(c,s)=>{s.events.push('b');s.registerCommand('temporary',()=>{});throw Error('broken')}`,
    'a.cjs': `exports.activate=(c,s)=>{s.events.push('a');const d=s.vscode.commands.registerCommand('solidityLean.runFunction',()=>42);c.subscriptions.push(d)}`,
    'ignored.js': `throw Error('must not load')`,
    'index.cjs': `throw Error('must not load')`
  });
  const registry = editor.activate({subscriptions:[]}, {vscode,output:{appendLine:x=>messages.push(x)},events}, dir);
  assert.deepEqual(events.slice(0,4), ['a','b','dispose temporary','z']);
  assert.match(messages[0], /b\.cjs.*broken/);
  assert.equal(commands.get('solidityLean.runFunction')(), 42);
  commands.get('solidityLean.showObligation')();
  assert.match(messages.at(-1), /not available in this build/);
  registry.dispose(); registry.dispose();
  assert.equal(commands.size, 0);
  assert.equal(events.filter(x=>x==='dispose solidityLean.runFunction').length,1);
  assert.ok(events.indexOf('dispose z') < events.indexOf('dispose solidityLean.runFunction'));
});

test('server commits features in order, advertises requests and lenses, and rolls back failures', async t => {
  const events = [], logs = [], peer = {requests:new Map(), onRequest(name,fn){this.requests.set(name,fn);}, notify(_method, params){logs.push(params.message);}};
  const dir = fixture(t, {
    'z.cjs': `exports.register=s=>{s.service.events.push('z');s.registerCodeLensProvider(()=>[{title:'z'}]);return {dispose(){s.service.events.push('dispose z')}}}`,
    'b.cjs': `exports.register=s=>{s.service.events.push('b');s.onRequest('solidityLean.bad',()=>1);s.registerCodeLensProvider(()=>[{title:'bad'}]);throw Error('broken')}`,
    'a.cjs': `exports.register=s=>{s.service.events.push('a');s.onRequest('solidityLean.good',()=>42);s.registerCodeLensProvider(()=>[{title:'a'}]);return {dispose(){s.service.events.push('dispose a')}}}`
  });
  const registry = server.register(peer,{events},dir);
  assert.deepEqual(events,['a','b','z']);
  assert.match(logs[0], /b\.cjs.*broken/);
  assert.deepEqual(registry.requests,['solidityLean.good']);
  assert.equal(registry.codeLens,true);
  assert.equal(peer.requests.get('solidityLean.good')(),42);
  assert.equal(peer.requests.has('solidityLean.bad'),false);
  assert.deepEqual(await peer.requests.get('textDocument/codeLens')({},1),[{title:'a'},{title:'z'}]);
  registry.dispose();registry.dispose();
  assert.equal(peer.requests.size,0);
  assert.deepEqual(events.slice(-2),['dispose z','dispose a']);
});
