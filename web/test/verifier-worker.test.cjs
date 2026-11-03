'use strict';
const {test,after}=require('node:test'),assert=require('node:assert/strict');
const {buildSync}=require('esbuild'),fs=require('node:fs'),os=require('node:os'),path=require('node:path');
const dir=fs.mkdtempSync(path.join(os.tmpdir(),'verifier-worker-test-'));
buildSync({entryPoints:[path.resolve(__dirname,'../browser/verifier-worker.mjs')],outfile:path.join(dir,'worker.cjs'),bundle:true,platform:'node',format:'cjs'});
const {VerifierWorker}=require(path.join(dir,'worker.cjs'));
class FakeWorker{
  constructor(){this.messages=[];}
  postMessage(m){this.messages.push(m);if(m.method==='boot')queueMicrotask(()=>this.reply(m.id,{ready:true}));}
  reply(id,result){this.onmessage?.({data:{id,result}});}
  terminate(){this.stopped=true;}
}
global.Worker=FakeWorker;
after(()=>{delete global.Worker;fs.rmSync(dir,{recursive:true,force:true});});
test('a short cancelled check drains and the same worker accepts a fresh result',async()=>{
 const transport=new VerifierWorker('/test-worker');
 try{
  const firstBoot=transport.boot();assert.equal(transport.boot(),firstBoot);await firstBoot;
  const worker=transport.worker,old=transport.request('check',{source:'old'});
  const oldId=worker.messages.at(-1).id;
  transport.abandon(undefined,1000);await assert.rejects(old,e=>e.code==='CANCELLED');
  const fresh=transport.request('check',{source:'fresh'}),freshId=worker.messages.at(-1).id;
  worker.reply(oldId,{wrongSource:true});worker.reply(freshId,{source:'fresh'});
  assert.deepEqual(await fresh,{source:'fresh'});assert.equal(transport.worker,worker);assert.equal(worker.stopped,undefined);
 }finally{transport.dispose();}
});
test('a cancelled check that does not drain stops within its grace period',async()=>{
 let restarted;const restart=new Promise(resolve=>{restarted=resolve;});
 const transport=new VerifierWorker('/test-worker',event=>{if(event.method==='restartRequired')restarted();});
 try{
  await transport.boot();const worker=transport.worker,old=transport.request('check');
  transport.abandon(undefined,10);await assert.rejects(old,e=>e.code==='CANCELLED');
  const queued=transport.request('check');const rejected=assert.rejects(queued,e=>e.code==='CANCELLED');
  await restart;await rejected;assert.equal(worker.stopped,true);
  await transport.boot();assert.notEqual(transport.worker,worker);
  const fresh=transport.request('check'),id=transport.worker.messages.at(-1).id;
  worker.reply(id,{stale:true});transport.worker.reply(id,{fresh:true});assert.deepEqual(await fresh,{fresh:true});
 }finally{transport.dispose();}
});
test('a timeout preserves its cause and permits a replacement worker',async()=>{
 const transport=new VerifierWorker('/test-worker');
 try{await transport.boot();await assert.rejects(transport.request('check',{},5),e=>e.code==='TIMEOUT');assert.equal(transport.worker,undefined);await transport.boot();assert.ok(transport.worker);}
 finally{transport.dispose();}
});
