'use strict';
// Protocol failure tests use an explicitly fake kernel. Successful proof and
// offline execution evidence comes only from website.cjs with the real WASM.
const test=require('node:test'),assert=require('node:assert/strict');
const fs=require('node:fs'),os=require('node:os'),path=require('node:path');
const {buildSync}=require('esbuild');
const directory=fs.mkdtempSync(path.join(os.tmpdir(),'browser-proof-protocol-'));
buildSync({entryPoints:[path.resolve(__dirname,'../browser/proofs.mjs')],outfile:path.join(directory,'proofs.cjs'),bundle:true,platform:'node',format:'cjs'});
const proofs=require(path.join(directory,'proofs.cjs'));
const declaration={id:2,nodeType:'FunctionDefinition',name:'f',src:'0:1:0'};
const compiled={fixture:{},primaryAst:{src:'0:1:0',nodes:[{id:1,nodeType:'ContractDefinition',name:'C',nodes:[declaration]}]},text:'{}',hash:'0',sourceHash:'source-hash'};
let response,bootResponse;
const workers=[];
class FakeKernelWorker {
  constructor(url){this.url=url;workers.push(this);}
  postMessage({id,method,params}){queueMicrotask(()=>{if(this.stopped)return;if(method==='boot'&&bootResponse){bootResponse(this,id);return;}if(method==='boot')this.onmessage({data:{id,result:{version:'4.24.0',build:'fake-test-only'}}});else response(this,id,params);});}
  terminate(){this.stopped=true;}
}
global.Worker=FakeKernelWorker;
const check=timeoutMs=>proofs.verifyInBrowser({compiled,text:'x',name:'C.sol',timeoutMs});
function reply(worker,id,params,code,rows){worker.onmessage({data:{id,result:{code,diagnostics:[],stderr:[],outputs:rows?{[params.outputs[0]]:JSON.stringify(rows)}:{}}}});}
test.after(()=>{proofs.cancelProofs();fs.rmSync(directory,{recursive:true,force:true});delete global.Worker;});
test.afterEach(()=>{proofs.cancelProofs();bootResponse=undefined;});
test('a nonzero Lean exit stays an error even with a partial checkpoint',async()=>{
  response=(worker,id,params)=>reply(worker,id,params,2,[{sourceId:2,function:'f',status:'pending'}]);
  const report=await check(1000);assert.equal(report.results.length,1);assert.equal(report.errors.length,1);assert.match(report.errors[0].reason,/exit 2/);
});
test('exit zero without a fresh checkpoint cannot be accepted',async()=>{
  response=(worker,id,params)=>reply(worker,id,params,0);
  await assert.rejects(check(1000),/fresh verification checkpoint/);
});
test('a checkpoint from a different declaration is rejected',async()=>{
  response=(worker,id,params)=>reply(worker,id,params,0,[{sourceId:99,function:'f',status:'pending'}]);
  await assert.rejects(check(1000),/selected declaration/);
});
test('terminating a timed out kernel preserves the timeout cause',async()=>{
  response=()=>{};await assert.rejects(check(10),error=>error.code==='TIMEOUT'&&/timed out/.test(error.message));
});
test('explicit cancellation rejects the active kernel request',async()=>{
  let started;const ready=new Promise(resolve=>{started=resolve;});response=()=>started();
  const pending=check(1000);await ready;proofs.cancelProofs();await assert.rejects(pending,error=>error.code==='CANCELLED');
});
test('a browser stack limit rejects the request with its explicit cause',async()=>{
  response=(worker,id)=>worker.onmessage({data:{id,error:{code:'BROWSER_STACK_LIMIT',message:'Browser proof checking exceeded its call-stack limit. No proof result was accepted.'}}});
  await assert.rejects(check(1000),error=>error.code==='BROWSER_STACK_LIMIT'&&/No proof result was accepted/.test(error.message));
});

test('cancelling a delayed direct boot cannot dispose its replacement',async()=>{
  let started;const bootStarted=new Promise(resolve=>{started=resolve;});
  bootResponse=(worker,id)=>started({worker,id});
  const old=proofs.prepareProofs();const first=await bootStarted;
  proofs.cancelProofs();const rejected=assert.rejects(old,e=>e.code==='CANCELLED');
  bootResponse=(worker,id)=>worker.onmessage({data:{id,result:{kind:'generated-c-wasm',version:'4.24.0'}}});
  const fresh=await proofs.prepareProofs();await rejected;
  first.worker.onmessage({data:{id:first.id,error:{message:'late old failure'}}});
  assert.equal(fresh.kind,'generated-c-wasm');assert.equal(workers.at(-1).stopped,undefined);
});
test('an edit during general-worker boot keeps its environment but submits no obsolete check',async()=>{
  let started;const bootStarted=new Promise(resolve=>{started=resolve;});
  bootResponse=(worker,id)=>{if(worker.url==='/direct-worker.js')worker.onmessage({data:{id,result:{}}});else started({worker,id});};
  let submitted=0;response=(worker,id,params)=>{submitted++;reply(worker,id,params,0,[{sourceId:2,function:'f',status:'pending'}]);};
  const old=check(1000),first=await bootStarted;proofs.abandonProofs();
  const rejected=assert.rejects(old,e=>e.code==='CANCELLED');
  first.worker.onmessage({data:{id:first.id,result:{version:'4.24.0'}}});await rejected;
  assert.equal(submitted,0);const report=await check(1000);
  assert.equal(report.results[0].status,'pending');assert.equal(submitted,1);assert.equal(first.worker.stopped,undefined);
});

test('a request deadline bounds lazy boot without destroying a shared environment',async()=>{
  let started;const bootStarted=new Promise(resolve=>{started=resolve;});
  bootResponse=(worker,id)=>{if(worker.url==='/direct-worker.js')worker.onmessage({data:{id,result:{}}});else started({worker,id});};
  let submitted=0;response=(worker,id,params)=>{submitted++;reply(worker,id,params,0,[{sourceId:2,function:'f',status:'pending'}]);};
  const pending=check(25),rejected=assert.rejects(pending,e=>e.code==='TIMEOUT'&&e.preserveRuntime===true),first=await bootStarted;
  await rejected;assert.equal(first.worker.stopped,undefined);assert.equal(submitted,0);
  first.worker.onmessage({data:{id:first.id,result:{version:'4.24.0'}}});
  assert.equal((await check(1000)).results[0].status,'pending');assert.equal(submitted,1);
});
