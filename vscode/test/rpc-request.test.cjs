// Injected framed-message controls; handlers only count calls, never run proof/product work.
'use strict';
const test=require('node:test'),assert=require('node:assert/strict'),{PassThrough}=require('node:stream'),{RpcPeer,LspFrames}=require('../src/rpc.cjs');
const frame=value=>{const body=Buffer.from(JSON.stringify(value));return Buffer.concat([Buffer.from(`Content-Length: ${body.length}\r\n\r\n`),body]);};
function fixture(){const input=new PassThrough(),output=new PassThrough(),peer=new RpcPeer(input,output);return{input,output,peer,close(){peer.close();input.destroy();output.destroy();}};}
for(const [name,patch]of Object.entries({objectId:{id:{}},arrayId:{id:[]},booleanId:{id:false},nullId:{id:null},numericMethod:{method:7},arrayMethod:{method:[]}})){
 test('malformed request refuses '+name+' before handler side effects and later notification',async()=>{
  const f=fixture();let work=0,notices=0;f.peer.onRequest('owned',()=>{work++;return null;});f.peer.onNotification('after',()=>notices++);
  try{const pending=f.peer.request('waiting',{}, {timeoutMs:1000}),rejected=assert.rejects(pending,/Malformed JSON-RPC request/);
   f.input.write(Buffer.concat([frame({jsonrpc:'2.0',id:1,method:'owned',params:{},...patch}),frame({jsonrpc:'2.0',method:'after',params:{}})]));
   await rejected;assert.equal(work,0);assert.equal(notices,0);assert.equal(f.peer.closed,true);assert.equal(f.peer.pending.size,0);
  }finally{f.close();}
 });
}
test('string and finite numeric request IDs remain exact and notifications need no ID',async()=>{
 const f=fixture(),replies=[],ids=[],frames=new LspFrames();frames.on('message',r=>replies.push(r));f.output.on('data',b=>frames.push(b));let notices=0;
 f.peer.onRequest('owned',(params,id)=>{ids.push(id);return params;});f.peer.onNotification('after',()=>notices++);
 try{for(const id of [0,'0','',-1,1.5])f.input.write(frame({jsonrpc:'2.0',id,method:'owned',params:{owned:true}}));f.input.write(frame({jsonrpc:'2.0',method:'after'}));
  await new Promise(setImmediate);assert.deepEqual(ids,[0,'0','',-1,1.5]);assert.deepEqual(replies.map(r=>r.id),ids);assert.ok(replies.every(r=>r.result.owned===true));assert.equal(notices,1);assert.equal(f.peer.closed,false);
 }finally{f.close();}
});

test('overflowing wire numeric ID cannot dispatch then serialize a different null ID',async()=>{
 const f=fixture();let work=0;f.peer.onRequest('owned',()=>work++);try{const pending=f.peer.request('waiting',{}, {timeoutMs:1000}),rejected=assert.rejects(pending,/Malformed JSON-RPC request/);
  const body=Buffer.from('{"jsonrpc":"2.0","id":1e400,"method":"owned","params":{}}');f.input.write(Buffer.concat([Buffer.from(`Content-Length: ${body.length}\r\n\r\n`),body]));await rejected;assert.equal(work,0);assert.equal(f.peer.closed,true);
 }finally{f.close();}
});
test('opposite directions may use the same valid ID without settling each other',async()=>{
 const f=fixture(),sent=[],frames=new LspFrames();frames.on('message',r=>sent.push(r));f.output.on('data',b=>frames.push(b));let work=0;
 f.peer.onRequest('owned',()=>{work++;return false;});try{const pending=f.peer.request('remote',{}, {timeoutMs:1000});f.input.write(frame({jsonrpc:'2.0',id:1,method:'owned',params:{}}));await new Promise(setImmediate);
  assert.equal(work,1);assert.equal(f.peer.pending.size,1);assert.ok(sent.some(r=>r.id===1&&r.result===false));f.input.write(frame({jsonrpc:'2.0',id:1,result:'remote reply'}));assert.equal(await pending,'remote reply');assert.equal(f.peer.pending.size,0);assert.equal(f.peer.closed,false);
 }finally{f.close();}
});
