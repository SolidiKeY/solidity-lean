// Injected VS Code boundary: observer return/error and source-session regression, not native UI/proof.
'use strict';
const test=require('node:test'),assert=require('node:assert/strict'),Module=require('node:module'),path=require('node:path'),{observe}=require('../parity/observe.cjs');
test('command observation preserves sync/async outcomes and binds real handler invocation sessions',async()=>{
 const events=[],handlers=new Map(),doc={uri:{toString:()=> 'file:///observed.sol'},version:1,isDirty:true,isClosed:false,getText:()=> 'contract C {}'},vscode={tests:{},workspace:{isTrusted:true},window:{activeTextEditor:{document:doc}},commands:{registerCommand:(id,fn,ctx)=>(handlers.set(id,fn.bind(ctx)),{dispose(){}})},languages:{onDidChangeDiagnostics:()=>({dispose(){}})}};
 const base=path.resolve('/observer-extension'),original=Module._load,observer=observe(vscode,(kind,data)=>events.push({kind,data}),base);
 try{const api=Module._load('vscode',{filename:path.join(base,'entry.cjs')});api.commands.registerCommand('sync',function(n){assert.equal(this.value,7);return n+1;},{value:7});assert.equal(handlers.get('sync')(3),4);
  api.commands.registerCommand('async',async()=>{doc.version++;return true;});assert.equal(await handlers.get('async')(),true);
  const failure=Error('authentic failure');api.commands.registerCommand('fail',()=>{throw failure;});assert.throws(()=>handlers.get('fail')(),e=>e===failure);
  api.commands.registerCommand('reject',()=>Promise.reject(failure));await assert.rejects(handlers.get('reject')(),e=>e===failure);
  const starts=events.filter(e=>e.kind==='command.start');assert.equal(starts.length,4);assert.equal(new Set(starts.map(e=>e.data.invocationId)).size,4);assert.equal(new Set(starts.map(e=>e.data.source.session)).size,1);assert.equal(starts[0].data.source.version,1);assert.equal(events.find(e=>e.kind==='command.end'&&e.data.id==='async').data.source.version,2);assert.equal(events.filter(e=>e.kind==='command.error').length,2);
  api.commands.registerCommand('null',()=>{throw null;});let caught=false;try{handlers.get('null')();}catch(value){caught=true;assert.equal(value,null);}assert.ok(caught);
  api.commands.registerCommand('undefined',()=>Promise.reject(undefined));caught=false;try{await handlers.get('undefined')();}catch(value){caught=true;assert.equal(value,undefined);}assert.ok(caught);
  const unprintable={[Symbol.toPrimitive](){throw Error('printer failed');}};api.commands.registerCommand('unprintable',()=>{throw unprintable;});assert.throws(()=>handlers.get('unprintable')(),value=>value===unprintable);
  const oldText=doc.getText;doc.getText=()=>{throw Error('document retired');};assert.equal(handlers.get('sync')(3),4);doc.getText=oldText;assert.ok(events.some(e=>e.data.source?.unavailable));
  observer.restore();const count=events.length;assert.equal(handlers.get('sync')(8),9);assert.equal(events.length,count);assert.equal(Module._load,original);
 }finally{observer.restore();}
});
