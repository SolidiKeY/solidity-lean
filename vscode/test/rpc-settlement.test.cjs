// Injected transport failures only; no native/server/proof acceptance claim.
'use strict';
const test=require('node:test'),assert=require('node:assert/strict'),{PassThrough}=require('node:stream'),{getEventListeners}=require('node:events'),{RpcPeer}=require('../src/rpc.cjs');
function fixture(){const input=new PassThrough(),output=new PassThrough(),peer=new RpcPeer(input,output);return{input,output,peer,dispose(){peer.close();input.destroy();output.destroy();}};}
for(const [name,reason]of [['null',null],['false',false],['zero',0],['empty',''],['frozen Error',Object.freeze(Error('transport failed'))]]){
 test('close with '+name+' rejects every pending request with the original reason',async()=>{
  const f=fixture(),controller=new AbortController();let closed;f.peer.on('close',reason=>closed=reason);
  try{const outcomes=Promise.allSettled([f.peer.request('first',{}, {signal:controller.signal,timeoutMs:1000}),f.peer.request('second',{}, {timeoutMs:1000})]);f.peer.close(reason);const rows=await outcomes;assert.deepEqual(rows.map(r=>r.status),['rejected','rejected']);assert.ok(rows.every(r=>r.reason===reason));assert.equal(closed,reason);assert.equal(f.peer.pending.size,0);assert.equal(getEventListeners(controller.signal,'abort').length,0);
  }finally{f.dispose();}
 });
}
for(const [name,reason]of [['null',null],['false',false],['zero',0],['empty',''],['undefined',undefined]]){
 test('initial write throwing '+name+' remains a rejected request',async t=>{
  const f=fixture(),controller=new AbortController();t.mock.method(f.output,'write',()=>{throw reason;});try{const [row]=await Promise.allSettled([f.peer.request('first',{}, {signal:controller.signal,timeoutMs:1000})]);assert.equal(row.status,'rejected');assert.equal(row.reason,reason);assert.equal(f.peer.pending.size,0);assert.equal(getEventListeners(controller.signal,'abort').length,0);
  }finally{f.dispose();}
 });
 test('cancel write throwing '+name+' closes other requests while preserving cancellation priority',async t=>{
  const f=fixture(),controller=new AbortController();try{const outcomes=Promise.allSettled([f.peer.request('first',{}, {signal:controller.signal,timeoutMs:1000}),f.peer.request('second',{}, {timeoutMs:1000})]);t.mock.method(f.output,'write',()=>{throw reason;});controller.abort();const [a,b]=await outcomes;assert.equal(a.status,'rejected');assert.equal(a.reason.code,-32800);assert.equal(b.status,'rejected');if(reason===undefined)assert.match(b.reason.message,/Connection closed/);else assert.equal(b.reason,reason);assert.equal(f.peer.closed,true);assert.equal(f.peer.pending.size,0);assert.equal(getEventListeners(controller.signal,'abort').length,0);
  }finally{f.dispose();}
 });
}
test('default undefined close keeps the existing Connection closed failure',async()=>{const f=fixture();try{const pending=f.peer.request('first',{}, {timeoutMs:1000}),rejected=assert.rejects(pending,/Connection closed/);f.peer.close(undefined);await rejected;}finally{f.dispose();}});
