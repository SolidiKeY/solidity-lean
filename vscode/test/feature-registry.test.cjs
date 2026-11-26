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

test('editor loads in sorted order, isolates failures, supplies fallbacks and disposes once', async t => {
  const events = [], messages = [], commands = new Map();
  const vscode = {commands:{registerCommand(name, handler) {
    assert.ok(!commands.has(name)); commands.set(name, handler);
    return {dispose() {events.push(`dispose ${name}`); commands.delete(name);}};
  }}, window:{showInformationMessage(message) {messages.push(message);}}};
  const dir = fixture(t, {
    'z.cjs': `exports.activate=(c,s)=>{s.events.push('z');c.subscriptions.push({dispose(){s.events.push('dispose z')}})}`,
    'b.cjs': `exports.activate=async(c,s)=>{s.events.push('b');s.registerCommand('temporary',()=>{});throw Error('broken')}`,
    'a.cjs': `exports.activate=(c,s)=>{s.events.push('a');const d=s.vscode.commands.registerCommand('solidityLean.runFunction',()=>42);c.subscriptions.push(d)}`,
    'ignored.js': `throw Error('must not load')`,
    'index.cjs': `throw Error('must not load')`
  });
  const registry = editor.create({subscriptions:[]}, {vscode,output:{appendLine:x=>messages.push(x)},events}, dir);
  commands.get('solidityLean.runFunction')();
  assert.match(messages.pop(), /not available in this build/);
  await registry.start({name:'ready'});
  assert.deepEqual(events.slice(0,4), ['a','b','dispose temporary','z']);
  assert.match(messages[0], /b\.cjs.*broken/);
  assert.equal(commands.get('solidityLean.runFunction')(), 42);
  commands.get('solidityLean.showObligation')();
  assert.match(messages.at(-1), /not available in this build/);
  await registry.dispose(); await registry.dispose();
  assert.equal(commands.size, 0);
  assert.equal(events.filter(x=>x==='dispose solidityLean.runFunction').length,1);
  assert.ok(events.indexOf('dispose z') < events.indexOf('dispose solidityLean.runFunction'));
});

test('server commits features in order, advertises requests and lenses, and rolls back failures', async t => {
  const events = [], logs = [], peer = {requests:new Map(), onRequest(name,fn){this.requests.set(name,fn);}, notify(_method, params){logs.push(params.message);}};
  const dir = fixture(t, {
    'z.cjs': `exports.register=s=>{s.service.events.push('z');s.registerCodeLensProvider(()=>{throw Error('lens broken')});s.registerCodeLensProvider(()=>[{title:'z'}]);return {dispose(){s.service.events.push('dispose z')}}}`,
    'b.cjs': `exports.register=async s=>{s.service.events.push('b');s.onRequest('solidityLean/bad',()=>1);s.registerCodeLensProvider(()=>[{title:'bad'}]);throw Error('broken')}`,
    'a.cjs': `exports.register=s=>{s.service.events.push('a');s.onRequest('solidityLean/good',()=>42);s.registerCodeLensProvider(()=>[{title:'a'}]);return {dispose(){s.service.events.push('dispose a')}}}`
  });
  const registry = await server.register(peer,{events},dir);
  assert.deepEqual(events,['a','b','z']);
  assert.match(logs[0], /b\.cjs.*broken/);
  assert.deepEqual(registry.requests,['solidityLean/good']);
  assert.equal(registry.codeLens,true);
  assert.equal(peer.requests.get('solidityLean/good')(),42);
  assert.equal(peer.requests.has('solidityLean/bad'),false);
  assert.deepEqual(await peer.requests.get('textDocument/codeLens')({},1),[{title:'a'},{title:'z'}]);
  assert.match(logs.at(-1), /z\.cjs.*lens broken/);
  await registry.dispose();await registry.dispose();
  assert.equal(peer.requests.size,0);
  assert.deepEqual(events.slice(-2),['dispose z','dispose a']);
});

test('disposal waits for in-flight activation and prevents late feature registration', async t => {
  const commands=new Map(),events=[];let release;
  const wait=new Promise(resolve=>{release=resolve;});
  const vscode={commands:{registerCommand(name,handler){commands.set(name,handler);return{dispose(){commands.delete(name);}};}},window:{showInformationMessage(){}}};
  const dir=fixture(t,{
    'a.cjs':`exports.activate=async(c,s)=>{s.events.push('start');await s.wait;c.subscriptions.push({dispose(){s.events.push('released')}});s.registerCommand('solidityLean.runFunction',()=>1)}`,
    'z.cjs':`exports.activate=(c,s)=>s.events.push('unexpected')`
  });
  const registry=editor.create({subscriptions:[]},{vscode,output:{appendLine(){}},events,wait},dir);
  const started=registry.start({});let done=false;
  const disposing=registry.dispose().then(()=>{done=true;});
  await Promise.resolve();assert.equal(done,false);
  release();await started;await disposing;
  assert.deepEqual(events,['start','released']);assert.equal(commands.size,0);
});

test('server initialize advertises and serves registered feature requests and lenses', async t => {
  const {PassThrough}=require('node:stream'),{pathToFileURL}=require('node:url');
  const {RpcPeer}=require('../src/rpc.cjs'),{startServer}=require('../src/lsp-server.cjs');
  const dir=fixture(t,{'feature.cjs':`exports.register=s=>{s.onRequest('solidityLean/show-example',p=>p);s.registerCodeLensProvider(()=>[{range:{start:{line:0,character:0},end:{line:0,character:1}},command:{title:'Example',command:'example'}}])}`});
  const original=server.register;server.register=(peer,service)=>original(peer,service,dir);
  const toServer=new PassThrough(),toClient=new PassThrough(),client=new RpcPeer(toClient,toServer),instance=startServer(toServer,toClient);
  try {
    const root=path.resolve(__dirname,'../..');
    const result=await client.request('initialize',{rootUri:pathToFileURL(root).href,capabilities:{},initializationOptions:{backendPath:root}});
    assert.deepEqual(result.capabilities.experimental.solidityLeanRequests,['solidityLean/show-example']);
    assert.equal(result.capabilities.codeLensProvider.resolveProvider,false);
    assert.deepEqual(await client.request('solidityLean/show-example',{value:7}),{value:7});
    assert.equal((await client.request('textDocument/codeLens',{}))[0].command.title,'Example');
    await client.request('shutdown');
  } finally {server.register=original;client.close();toServer.destroy();toClient.destroy();await instance.service?.dispose();}
});

test('extension activates features once after client identity and dispatches commands', async t => {
  const {fixture:editorFixture}=require('./controller-fixture.cjs'),{EventEmitter}=require('node:events');
  const Module=require('node:module'),load=Module._load,clients=require('../src/lsp-client.cjs'),originalClass=clients.LanguageServers,originalCreate=editor.create;
  const e=editorFixture();await e.api.dispose();const context={subscriptions:[]},notices=[],events=[];let lensProvider,refreshes=0,requests=0;
  e.vscode.window.showInformationMessage=message=>notices.push(message);
  e.vscode.EventEmitter=class {constructor(){this.event=()=>{};}fire(){refreshes++;}dispose(){}};
  e.vscode.CodeLens=class {constructor(range,command){this.range=range;this.command=command;}};
  e.vscode.languages.registerCodeLensProvider=(_selector,provider)=>{lensProvider=provider;return {dispose(){}};};
  const dir=fixture(t,{'a.cjs':`exports.activate=(c,s)=>{s.events.push(s.identity.serverInfo.version);s.registerCommand('solidityLean.runFunction',()=>99)}`});
  let instance;
  class Servers extends EventEmitter {constructor(){super();instance=this;} async open(){return {capabilities:{codeLensProvider:true}};} async request(){requests++;return [{range:{start:{line:0,character:0},end:{line:0,character:1}},command:{title:'lens',command:'x'}}];} cancel(){} save(){} close(){} async restart(){} async dispose(){} }
  clients.LanguageServers=Servers;
  editor.create=(ctx,services)=>originalCreate(ctx,{...services,events},dir);
  Module._load=function(name,...args){return name==='vscode'?e.vscode:load.call(this,name,...args);};
  let api;
  try {
    api=require('../src/extension.cjs').activate(context);
    assert.deepEqual(events,[]);
    e.commands.get('solidityLean.runFunction')();assert.match(notices.pop(),/not available in this build/);
    instance.emit('identity',{serverInfo:{version:'ready'}});instance.emit('identity',{serverInfo:{version:'again'}});
    await new Promise(resolve=>setImmediate(resolve));
    assert.deepEqual(events,['ready']);assert.equal(e.commands.get('solidityLean.runFunction')(),99);
    assert.equal((await lensProvider.provideCodeLenses(e.doc)).length,1);assert.equal(requests,1);
    e.config.codeLens=false;e.events.configuration({affectsConfiguration:key=>key==='solidityLean.codeLens'});
    assert.equal(refreshes,1);assert.deepEqual(await lensProvider.provideCodeLenses(e.doc),[]);assert.equal(requests,1);
  } finally {Module._load=load;clients.LanguageServers=originalClass;editor.create=originalCreate;await api?.dispose();}
  assert.equal(e.commands.has('solidityLean.runFunction'),false);
});

test('registry disposal awaits asynchronous feature cleanup', async t => {
  const commands=new Map(),events=[];let release;
  const wait=new Promise(resolve=>{release=resolve;});
  const vscode={commands:{registerCommand(n,f){commands.set(n,f);return{dispose(){commands.delete(n);}};}},window:{showInformationMessage(){}}};
  const dir=fixture(t,{'a.cjs':`exports.activate=(c,s)=>({async dispose(){s.events.push('disposing');await s.wait;s.events.push('disposed')}})`});
  const registry=editor.create({subscriptions:[]},{vscode,output:{appendLine(){}},events,wait},dir);await registry.start({});
  let done=false;const closing=registry.dispose().then(()=>{done=true;});await new Promise(resolve=>setImmediate(resolve));
  assert.equal(done,false);assert.deepEqual(events,['disposing']);release();await closing;assert.deepEqual(events,['disposing','disposed']);assert.equal(commands.size,0);
});
