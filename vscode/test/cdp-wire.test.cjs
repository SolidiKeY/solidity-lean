// Actual loopback WebSocket transport with synthetic CDP payloads, not native UI evidence.
'use strict';
const test=require('node:test'),assert=require('node:assert/strict'),http=require('node:http');
const {createHash}=require('node:crypto'),{once}=require('node:events');
const {DevTools}=require('../parity/renderer.cjs');
const digest=value=>createHash('sha256').update(value).digest('hex');
function frame(payload,opcode=1,fin=true){
 payload=Buffer.isBuffer(payload)?payload:Buffer.from(payload);let header;
 if(payload.length<126){header=Buffer.alloc(2);header[1]=payload.length;}
 else if(payload.length<=65535){header=Buffer.alloc(4);header[1]=126;header.writeUInt16BE(payload.length,2);}
 else{header=Buffer.alloc(10);header[1]=127;header.writeBigUInt64BE(BigInt(payload.length),2);}
 header[0]=(fin?128:0)|opcode;return Buffer.concat([header,payload]);
}
async function wire(t,respond){
 const sockets=new Set(),requests=[],events=[],serverErrors=[];let client;
 const server=http.createServer((req,res)=>{res.writeHead(404);res.end();});
 server.on('upgrade',(request,socket,head)=>{
  sockets.add(socket);socket.on('close',()=>sockets.delete(socket));socket.on('error',error=>serverErrors.push(error.message));
  const accept=createHash('sha1').update(request.headers['sec-websocket-key']+'258EAFA5-E914-47DA-95CA-C5AB0DC85B11').digest('base64');
  socket.write('HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Accept: '+accept+'\r\n\r\n');
  let pending=head,responding=false;
  const consume=()=>{
   try{while(pending.length>=2){
    const opcode=pending[0]&15,masked=!!(pending[1]&128);let length=pending[1]&127,offset=2;
    if(length===126){if(pending.length<4)return;length=pending.readUInt16BE(2);offset=4;}
    if(length===127){if(pending.length<10)return;const wide=pending.readBigUInt64BE(2);assert.ok(wide<=65536n);length=Number(wide);offset=10;}
    assert.ok(masked,'Client frame must be masked');assert.ok(length<=65536,'Synthetic request bound');
    if(pending.length<offset+4+length)return;
    const mask=pending.subarray(offset,offset+4),body=Buffer.from(pending.subarray(offset+4,offset+4+length));pending=pending.subarray(offset+4+length);
    for(let i=0;i<body.length;i++)body[i]^=mask[i%4];
    if(opcode===8){socket.end(frame(body,8));continue;}
    assert.equal(opcode,1);assert.equal(responding,false);responding=true;
    const request=JSON.parse(body.toString('utf8'));requests.push(request);
    Promise.resolve(respond(socket,request)).catch(error=>{serverErrors.push(error.message);socket.destroy();});
   }}catch(error){serverErrors.push(error.message);socket.destroy();}
  };
  socket.on('data',chunk=>{pending=Buffer.concat([pending,chunk]);consume();});consume();
 });
 await new Promise((resolve,reject)=>{server.once('error',reject);server.listen(0,'127.0.0.1',resolve);});
 t.after(async()=>{client?.close();const closed=[...sockets].map(socket=>new Promise(resolve=>socket.once('close',resolve)));for(const socket of sockets)socket.destroy();await Promise.all([...closed,new Promise(resolve=>server.close(resolve))]);assert.equal(sockets.size,0);assert.deepEqual(serverErrors,[]);});
 client=new DevTools('ws://127.0.0.1:'+server.address().port+'/owned',{diagnostic:event=>events.push(event),identity:{targetId:'synthetic-loopback'}});
 return{client,requests,events};
}
async function send(socket,bytes){if(!socket.write(bytes))await once(socket,'drain');}
const options={timeout:6000};
for(const fragmented of [false,true])test('runtime WebSocket preserves large UTF8 '+(fragmented?'fragmented':'single-frame')+' CDP response',options,async t=>{
 const text='λ😀'.repeat(80000),result={documents:[{synthetic:true}],strings:[text]},payload=Buffer.from(JSON.stringify({id:1,result}));
 const f=await wire(t,async(socket,request)=>{
  assert.equal(request.method,'DOMSnapshot.captureSnapshot');assert.deepEqual(request.params,{computedStyles:[]});
  if(!fragmented){await send(socket,frame(payload));return;}
  // Split within an emoji and across the16-bit frame-length boundary.
  const first=payload.indexOf(Buffer.from('😀'))+1,second=first+65536;
  for(const bytes of [frame(payload.subarray(0,first),1,false),frame(payload.subarray(first,second),0,false),frame(payload.subarray(second),0,true)])await send(socket,bytes);
 });
 const observed=await f.client.request('DOMSnapshot.captureSnapshot',{computedStyles:[]});
 assert.equal(observed.strings[0].length,text.length);assert.equal(digest(observed.strings[0]),digest(text));assert.deepEqual(observed.documents,result.documents);
 assert.equal(f.requests.length,1);assert.equal(f.events.filter(e=>e.event==='response').length,1);assert.ok(f.events.find(e=>e.event==='response').bytes>450000);f.client.finish();
});
test('runtime WebSocket refuses a disconnect in an incomplete fragmented CDP response',options,async t=>{
 const f=await wire(t,async socket=>{await send(socket,frame('{"id":1,"result":{"documents":[',1,false));socket.destroy();});
 await assert.rejects(f.client.request('DOMSnapshot.captureSnapshot'),/disconnected|connection failed/);
 assert.equal(f.events.filter(e=>e.event==='response').length,0);assert.equal(f.client.pending.size,0);assert.throws(()=>f.client.finish(),/disconnected|connection failed/);
});
test('wire notification and unrelated response cannot satisfy the current request',options,async t=>{
 const f=await wire(t,async socket=>{for(const value of [{method:'Page.lifecycleEvent',params:{synthetic:true}},{id:77,result:{foreign:true}},{id:1,result:{owned:true}}])await send(socket,frame(JSON.stringify(value)));});
 assert.deepEqual(await f.client.request('Runtime.evaluate'),{owned:true});assert.equal(f.events.filter(e=>e.event==='notification').length,1);assert.ok(f.events.some(e=>e.event==='response.unmatched'&&e.id===77));assert.equal(f.events.find(e=>e.event==='response').id,1);f.client.finish();
});
for(const binary of [false,true])test('wire '+(binary?'binary':'malformed JSON')+' message aborts pending CDP work',options,async t=>{
 const f=await wire(t,async socket=>{await send(socket,frame(binary?JSON.stringify({id:1,result:{untrusted:true}}):'not JSON',binary?2:1));});
 await assert.rejects(f.client.request('Runtime.evaluate'),/Malformed CDP response/);assert.equal(f.client.pending.size,0);assert.equal(f.events.filter(e=>e.event==='response').length,0);assert.throws(()=>f.client.finish(),/Malformed CDP response/);
});
