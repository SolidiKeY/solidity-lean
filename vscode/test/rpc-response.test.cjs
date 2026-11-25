// Injected byte-transport controls only; no native or proof claim.
'use strict';
const test=require('node:test'),assert=require('node:assert/strict'),{PassThrough}=require('node:stream'),{RpcPeer}=require('../src/rpc.cjs');
const frame=message=>{const body=Buffer.from(JSON.stringify(message));return Buffer.concat([Buffer.from(`Content-Length: ${body.length}\r\n\r\n`),body]);};
function fixture(){const input=new PassThrough(),output=new PassThrough(),peer=new RpcPeer(input,output);return{input,peer,close(){peer.close();input.destroy();output.destroy();}};}
for(const [name,response]of Object.entries({missing:{},both:{result:null,error:{code:-1,message:'failure'}},nullError:{error:null},stringError:{error:'failure'},fractionalCode:{error:{code:1.5,message:'failure'}},missingMessage:{error:{code:-1}},numericMessage:{error:{code:-1,message:7}}})){
 test('malformed matching response refuses '+name+' without delivering later coalesced notifications',async()=>{
  const f=fixture();let delivered=0;f.peer.onNotification('changed',()=>delivered++);
  try{const a=f.peer.request('configuration',{}, {timeoutMs:1000}),b=f.peer.request('symbols',{}, {timeoutMs:1000});
   const rejected=Promise.all([assert.rejects(a,/Malformed JSON-RPC response/),assert.rejects(b,/Malformed JSON-RPC response/)]);
   f.input.write(Buffer.concat([frame({jsonrpc:'2.0',id:1,...response}),frame({jsonrpc:'2.0',method:'changed',params:{}})]));
   await rejected;assert.equal(f.peer.closed,true);assert.equal(f.peer.pending.size,0);assert.equal(delivered,0);
  }finally{f.close();}
 });
}
test('valid false zero null and error responses retain their values and exact request IDs',async()=>{
 const f=fixture();try{
  for(const value of [false,0,null]){const pending=f.peer.request('configuration',{}, {timeoutMs:1000});f.input.write(frame({jsonrpc:'2.0',id:f.peer.next,result:value}));assert.equal(await pending,value);assert.equal(f.peer.closed,false);}
  const pending=f.peer.request('configuration',{}, {timeoutMs:1000}),rejected=assert.rejects(pending,e=>e.code===-32602&&e.message==='bad settings'&&e.data.uri==='file:///owned.sol');f.input.write(frame({jsonrpc:'2.0',id:f.peer.next,error:{code:-32602,message:'bad settings',data:{uri:'file:///owned.sol'}}}));await rejected;assert.equal(f.peer.closed,false);
 }finally{f.close();}
});

test('foreign and differently typed IDs cannot settle the current request',async()=>{
 const f=fixture();try{let settled=false;const pending=f.peer.request('configuration',{}, {timeoutMs:1000}).then(value=>{settled=true;return value;});
  f.input.write(frame({jsonrpc:'2.0',id:'1',result:'foreign'}));f.input.write(frame({jsonrpc:'2.0',id:999,result:'foreign'}));await Promise.resolve();assert.equal(settled,false);assert.equal(f.peer.closed,false);assert.equal(f.peer.pending.size,1);
  f.input.write(frame({jsonrpc:'2.0',id:1,result:'owned'}));assert.equal(await pending,'owned');assert.equal(f.peer.pending.size,0);
 }finally{f.close();}
});
