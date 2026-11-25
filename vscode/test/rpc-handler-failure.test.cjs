// Injected handlers and byte transport only; no native/proof acceptance.
'use strict';
const test=require('node:test'),assert=require('node:assert/strict'),{PassThrough}=require('node:stream'),{RpcPeer}=require('../src/rpc.cjs');
function pair(){const a=new PassThrough(),b=new PassThrough(),client=new RpcPeer(a,b),server=new RpcPeer(b,a);return{client,server,dispose(){client.close();server.close();a.destroy();b.destroy();}};}
for(const [name,reason]of [['null',null],['undefined',undefined],['false',false],['zero',0],['string','handler failed']]){
 for(const asyncFailure of [false,true])test((asyncFailure?'async ':'sync ')+name+' handler failure returns a valid InternalError',async()=>{
  const f=pair();f.server.onRequest('owned',()=>{if(asyncFailure)return Promise.reject(reason);throw reason;});try{await assert.rejects(f.client.request('owned',{}, {timeoutMs:1000}),e=>e.code===-32603&&e.message==='Request owned failed unexpectedly without providing any details.');assert.equal(f.client.pending.size,0);assert.equal(f.client.closed,false);assert.equal(f.server.closed,false);f.server.onRequest('owned',()=>false);assert.equal(await f.client.request('owned',{}, {timeoutMs:1000}),false);}finally{f.dispose();}
 });
}
test('frozen structured error fields retain their existing wire values',async()=>{
 const f=pair(),reason=Object.freeze(Object.assign(Error('exact message'),{code:-32042,data:{uri:'file:///owned.sol'}}));f.server.onRequest('owned',()=>{throw reason;});try{await assert.rejects(f.client.request('owned',{}, {timeoutMs:1000}),e=>e.code===reason.code&&e.message===reason.message&&e.data.uri===reason.data.uri);assert.equal(f.server.closed,false);}finally{f.dispose();}
});
for(const [name,result]of [['BigInt',1n],['cycle',(()=>{const value={};value.self=value;return value;})()]])test('unserializable '+name+' response closes the peer and rejects pending work',async()=>{
 const input=new PassThrough(),output=new PassThrough(),peer=new RpcPeer(input,output);peer.onRequest('owned',()=>result);try{const pending=peer.request('waiting',{}, {timeoutMs:1000}),rejected=assert.rejects(pending,/BigInt|circular/i),body=Buffer.from(JSON.stringify({jsonrpc:'2.0',id:9,method:'owned',params:{}}));input.write(Buffer.concat([Buffer.from(`Content-Length: ${body.length}\r\n\r\n`),body]));await rejected;assert.equal(peer.closed,true);assert.equal(peer.pending.size,0);}finally{peer.close();input.destroy();output.destroy();}
});

test('zero code, empty message and falsy error data remain valid rejection fields',async()=>{
 const f=pair();f.server.onRequest('owned',()=>{throw Object.freeze({code:0,message:'',data:false});});try{await assert.rejects(f.client.request('owned',{}, {timeoutMs:1000}),e=>e.code===0&&e.message===''&&e.data===false);assert.equal(f.client.closed,false);assert.equal(f.server.closed,false);}finally{f.dispose();}
});
for(const reason of [null,Object.freeze(Error('response write failed'))])test('response write failure closes pending transport work',async t=>{
 const input=new PassThrough(),output=new PassThrough(),peer=new RpcPeer(input,output);peer.onRequest('owned',()=>42);try{const pending=peer.request('waiting',{}, {timeoutMs:1000}),outcome=Promise.allSettled([pending]);t.mock.method(output,'write',()=>{throw reason;});const body=Buffer.from(JSON.stringify({jsonrpc:'2.0',id:9,method:'owned',params:{}}));input.write(Buffer.concat([Buffer.from(`Content-Length: ${body.length}\r\n\r\n`),body]));const [row]=await outcome;assert.equal(row.status,'rejected');assert.equal(row.reason,reason);assert.equal(peer.closed,true);assert.equal(peer.pending.size,0);
 }finally{peer.close();input.destroy();output.destroy();}
});
