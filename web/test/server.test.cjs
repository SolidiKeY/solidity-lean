'use strict';
const {test} = require('node:test');
const assert = require('node:assert/strict');
const {EventEmitter, once} = require('node:events');
const fs = require('node:fs');
const os = require('node:os');
const path = require('node:path');
const {WebSocket} = require('ws');
const {createServer} = require('../server.cjs');

class FixtureClient extends EventEmitter {
  constructor(config) {super(); this.config=config; this.ready=Promise.resolve(); this.docs=new Map(); this.peer={notify(){},request:async()=>({})};}
  async sync(doc) {this.docs.set(doc.uri.toString(),doc.getText());}
  async request(method,doc,params) {return {method,text:doc.getText(),params};}
  async verify(doc) {await new Promise(resolve=>setTimeout(resolve,20));return {results:[],errors:[],version:doc.version};}
  closeDocument(uri) {this.docs.delete(uri);}
  cancel() {}
  async dispose() {this.disposed=true;}
}
async function fixture(t, Client = FixtureClient) {
  const root=fs.mkdtempSync(path.join(os.tmpdir(),'offline-ide-test-'));
  const app=createServer({port:0,Client,backendPath:root});const url=await app.listen();
  t.after(async()=>{await app.close();fs.rmSync(root,{recursive:true,force:true});});
  const ws=new WebSocket(url.replace('http','ws')+'/lsp',{origin:url});await once(ws,'open');
  let id=0;const pending=new Map();ws.on('message',data=>{const message=JSON.parse(data);const p=pending.get(message.id);if(!p)return;pending.delete(message.id);message.error?p.reject(new Error(message.error.message)):p.resolve(message.result);});
  const rpc=(method,params)=>new Promise((resolve,reject)=>{const request=++id;pending.set(request,{resolve,reject});ws.send(JSON.stringify({id:request,method,params}));});
  return {app,url,root,ws,rpc};
}
test('serves only bundled application assets, with an offline content policy',async t=>{
  const {url}=await fixture(t);const page=await fetch(url);assert.equal(page.status,200);
  const csp=page.headers.get('content-security-policy');assert.match(csp,/connect-src 'self'/);assert.doesNotMatch(csp,/https:/);
  assert.match(await page.text(),/Solidity Lean/);
  const boot=await (await fetch(url+'/api/bootstrap')).json();assert.ok(boot.files['Counter.sol'].includes('openGoal'));
  for(const name of ['/server.cjs','/package.json','/../AGENTS.md','/vendor/vs/../../server.cjs','/media/nope.svg'])assert.equal((await fetch(url+name)).status,404,name);
  assert.equal((await fetch(url,{method:'POST'})).status,405);
});
test('rejects cross-origin websocket connections',async t=>{
  const {url}=await fixture(t);const ws=new WebSocket(url.replace('http','ws')+'/lsp',{origin:'https://untrusted.example'});
  const error=await new Promise(resolve=>ws.once('error',resolve));assert.match(error.message,/403/);
});
test('syncs exact unsaved buffers and rejects stale versions and escaped paths',async t=>{
  const {rpc}=await fixture(t);
  for(const name of ['../Escape.sol','/tmp/Escape.sol','Not.txt','a/b.sol'])await assert.rejects(rpc('open',{name,text:'contract A {}',version:1}),/Invalid document/);
  const first=await rpc('open',{name:'A.sol',text:'contract A {}',version:1});assert.match(first.uri,/session-.*\/A.sol$/);
  await assert.rejects(rpc('change',{name:'A.sol',text:'obsolete',version:1}),/version must increase/);
  await rpc('change',{name:'A.sol',text:'contract A { uint unsaved; }',version:2});
  const result=await rpc('textDocument/hover',{name:'A.sol',version:2,position:{line:0,character:5},textDocument:{uri:'file:///etc/passwd'}});
  assert.equal(result.text,'contract A { uint unsaved; }');assert.equal(result.params.textDocument,undefined);
  await assert.rejects(rpc('verify',{name:'A.sol',version:1}),/content changed/);
  await assert.rejects(rpc('textDocument/hover',{name:'A.sol',version:1}),/content changed/);
  await assert.rejects(rpc('shell',{command:'true'}),/not allowed/);
});
test('serializes pipelined edits, bounds open documents, and saves only inside the session',async t=>{
  const {rpc,root,ws}=await fixture(t);
  await rpc('open',{name:'A.sol',text:'one',version:1});
  await Promise.all([rpc('change',{name:'A.sol',text:'two',version:2}),rpc('change',{name:'A.sol',text:'three',version:3})]);
  assert.equal((await rpc('textDocument/hover',{name:'A.sol',version:3})).text,'three');
  for(const name of ['B.sol','C.sol','D.sol'])await rpc('open',{name,text:'contract A {}',version:1});
  await assert.rejects(rpc('open',{name:'E.sol',text:'',version:1}),/maximum four/);
  await rpc('close',{name:'B.sol'});await rpc('open',{name:'E.sol',text:'',version:1});
  await rpc('save',{name:'A.sol'});const base=path.join(root,'.lake/web-ide');const session=path.join(base,fs.readdirSync(base)[0]);
  assert.equal(fs.readFileSync(path.join(session,'A.sol'),'utf8'),'three');
  ws.close();await once(ws,'close');await new Promise(resolve=>setTimeout(resolve,30));assert.equal(fs.existsSync(session),false);
});
test('isolates browser sessions and validates settings',async t=>{
  const {url,rpc}=await fixture(t);await rpc('open',{name:'A.sol',text:'secret buffer',version:1});
  await assert.rejects(rpc('configure',{workers:100}),/Workers/);await assert.rejects(rpc('configure',{automaticVerification:'remote'}),/Invalid/);
  const ws=new WebSocket(url.replace('http','ws')+'/lsp',{origin:url});await once(ws,'open');
  const response=once(ws,'message');ws.send(JSON.stringify({id:1,method:'textDocument/hover',params:{name:'A.sol',version:1}}));
  assert.match(JSON.parse((await response)[0]).error.message,/Unknown/);ws.close();
});
test('materializes unopened workspace files and preserves closed dirty buffers',async t=>{
  const {rpc,root}=await fixture(t);
  await rpc('workspace',{files:{'A.sol':'import "./B.sol"; contract A is B {}','B.sol':'contract B {}'}});
  await assert.rejects(rpc('workspace',{files:{'../Escape.sol':'no'}}),/Invalid workspace files/);
  const base=path.join(root,'.lake/web-ide'),session=path.join(base,fs.readdirSync(base)[0]);
  assert.equal(fs.readFileSync(path.join(session,'B.sol'),'utf8'),'contract B {}');
  await rpc('open',{name:'B.sol',text:'contract B { uint changed; }',version:1});
  await rpc('close',{name:'B.sol'});
  assert.equal(fs.readFileSync(path.join(session,'B.sol'),'utf8'),'contract B { uint changed; }');
});
test('a disconnect during restart cannot create a replacement language server',async t=>{
  let created=0;
  class SlowClient extends FixtureClient {
    constructor(config){super(config);created++;}
    dispose(){return this.disposal ||= new Promise(resolve=>setTimeout(resolve,50));}
  }
  const {rpc,ws,root}=await fixture(t,SlowClient);await rpc('open',{name:'A.sol',text:'contract A {}',version:1});
  rpc('restart').catch(()=>{});await new Promise(resolve=>setTimeout(resolve,10));ws.close();await once(ws,'close');
  await new Promise(resolve=>setTimeout(resolve,80));assert.equal(created,1);
  assert.deepEqual(fs.readdirSync(path.join(root,'.lake/web-ide')),[]);
});
test('configuration changes retain the session project root',async t=>{
  let config;
  class ConfigClient extends FixtureClient {constructor(c){super(c);this.peer.notify=(method,params)=>{if(method==='workspace/didChangeConfiguration')config=params.settings;};}}
  const {rpc,root}=await fixture(t,ConfigClient);await rpc('open',{name:'A.sol',text:'contract A {}',version:1});
  await rpc('configure',{workers:2});assert.ok(config.projectRoot.startsWith(path.join(root,'.lake/web-ide')));assert.equal(config.timeoutMs,120000);assert.equal(config.workers,2);
});
test('large valid workspace snapshots fit the bounded transport',async t=>{
  const {rpc}=await fixture(t);const text=' '.repeat(5*1024*1024);
  const result=await rpc('workspace',{files:{'A.sol':text,'B.sol':text}});assert.equal(result.updated,2);
});
test('server shutdown waits for a disconnected session already disposing',async t=>{
  let disposed=false;
  class SlowClient extends FixtureClient {dispose(){return this.disposal ||= new Promise(resolve=>setTimeout(()=>{disposed=true;resolve();},60));}}
  const {rpc,ws,app}=await fixture(t,SlowClient);await rpc('open',{name:'A.sol',text:'contract A {}',version:1});
  ws.close();await once(ws,'close');await app.close();assert.equal(disposed,true);
});
