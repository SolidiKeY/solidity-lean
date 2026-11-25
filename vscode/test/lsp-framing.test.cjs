// Byte-framing controls only; these messages are not native parity observations.
'use strict';
const test=require('node:test'),assert=require('node:assert/strict');
const consumers=[['RPC',require('../src/rpc.cjs').LspFrames],['recorder',require('../parity/core.cjs').LspFrames]];
function frame(headerBytes,message={id:1,result:'é🦀'}){
  const body=Buffer.from(JSON.stringify(message));
  const prefix=Buffer.from(`Content-Length: ${body.length}\r\nX-Pad: `),suffix=Buffer.from('\r\n\r\n');
  const header=Buffer.concat([prefix,Buffer.alloc(headerBytes-prefix.length-suffix.length,120),suffix]);
  assert.equal(header.length,headerBytes);
  return Buffer.concat([header,body]);
}
function feed(parser,bytes,size){for(let i=0;i<bytes.length;i+=size)parser.push(bytes.subarray(i,i+size));}
for(const [name,Frames]of consumers){
  test(name+' admits bounded headers and coalesced UTF-8 frames regardless of fragmentation',()=>{
    const messages=[{id:1,result:'é🦀'},{id:2,result:'next'}];
    for(const headerBytes of [8191,8192]){
      const bytes=Buffer.concat(messages.map(message=>frame(headerBytes,message)));
      for(const size of [1,7,8192,bytes.length]){
        const parser=new Frames(),actual=[];parser.on('message',m=>actual.push(m));
        feed(parser,bytes,size);parser.end();assert.deepEqual(actual,messages);
      }
    }
  });
  test(name+' refuses oversized headers in both coalesced and fragmented deliveries',()=>{
    for(const headerBytes of [8193,9000]){
      const bytes=frame(headerBytes);
      for(const size of [bytes.length,1,7,8192]){
        const parser=new Frames(),actual=[];parser.on('message',m=>actual.push(m));
        assert.throws(()=>feed(parser,bytes,size),/Oversize LSP header/);
        assert.deepEqual(actual,[]);
      }
    }
  });
}

test('RPC and recorder share one framing implementation without changing body limits',()=>{
  assert.equal(consumers[0][1],consumers[1][1]);
  for(const [,Frames]of consumers){
    assert.equal(new Frames().limit,32*1024*1024);
    assert.throws(()=>new Frames(1).push(frame(40,{})),/Oversize LSP body/);
  }
});

test('oversized RPC header closes pending work before dispatching a notification',async()=>{
  const {PassThrough}=require('node:stream'),{RpcPeer}=require('../src/rpc.cjs');
  const input=new PassThrough(),output=new PassThrough(),peer=new RpcPeer(input,output);let delivered=0;
  peer.onNotification('textDocument/didOpen',()=>{delivered++;});
  try{
    const pending=peer.request('waiting',{}, {timeoutMs:1000});
    const rejected=assert.rejects(pending,/Oversize LSP header/);
    input.write(frame(8193,{jsonrpc:'2.0',method:'textDocument/didOpen',params:{uri:'file:///owned.sol'}}));
    await rejected;assert.equal(peer.closed,true);assert.equal(peer.pending.size,0);assert.equal(delivered,0);
  }finally{peer.close();input.destroy();output.destroy();}
});

for(const [name,Frames]of consumers){
 test(name+' refuses malformed UTF-8 before delivering replacement-character JSON',()=>{
  for(const bad of [[0xff],[0xc0,0xaf],[0xed,0xa0,0x80],[0xf0,0x9f]]){
   const body=Buffer.concat([Buffer.from('{"uri":"file:///'),Buffer.from(bad),Buffer.from('.sol"}')]);
   const bytes=Buffer.concat([Buffer.from(`Content-Length: ${body.length}\r\n\r\n`),body]);
   for(const size of [1,bytes.length]){const parser=new Frames(),actual=[];parser.on('message',m=>actual.push(m));assert.throws(()=>feed(parser,bytes,size),/encoding|UTF-8/i);assert.deepEqual(actual,[]);}
  }
 });
 test(name+' preserves legitimate replacement characters and a JSON BOM remains refused',()=>{
  const body=Buffer.from(JSON.stringify({uri:'file:///�.sol'})),parser=new Frames(),actual=[];parser.on('message',m=>actual.push(m));parser.push(Buffer.concat([Buffer.from(`Content-Length: ${body.length}\r\n\r\n`),body]));assert.deepEqual(actual,[{uri:'file:///�.sol'}]);
  const bom=Buffer.concat([Buffer.from([239,187,191]),Buffer.from('{}')]);assert.throws(()=>new Frames().push(Buffer.concat([Buffer.from(`Content-Length: ${bom.length}\r\n\r\n`),bom])));
 });
}

for(const [name,Frames]of consumers){
 test(name+' does not normalize high-bit header bytes into ASCII fields',()=>{
  for(const index of [0,16]){
   const bytes=Buffer.from('Content-Length: 2\r\n\r\n{}');bytes[index]|=0x80;
   for(const size of [1,bytes.length]){const parser=new Frames(),actual=[];parser.on('message',m=>actual.push(m));assert.throws(()=>feed(parser,bytes,size),/Non-ASCII LSP header/);assert.deepEqual(actual,[]);}
  }
 });
}

test('non-ASCII RPC header rejects pending work before notification delivery',async()=>{
 const {PassThrough}=require('node:stream'),{RpcPeer}=require('../src/rpc.cjs');
 const input=new PassThrough(),output=new PassThrough(),peer=new RpcPeer(input,output);let delivered=0;peer.onNotification('changed',()=>delivered++);
 try{const pending=peer.request('waiting',{}, {timeoutMs:1000}),rejected=assert.rejects(pending,/Non-ASCII LSP header/);
  const body=Buffer.from(JSON.stringify({jsonrpc:'2.0',method:'changed',params:{}})),header=Buffer.from(`Content-Length: ${body.length}\r\n\r\n`);header[0]|=0x80;input.write(Buffer.concat([header,body]));
  await rejected;assert.equal(peer.closed,true);assert.equal(peer.pending.size,0);assert.equal(delivered,0);
 }finally{peer.close();input.destroy();output.destroy();}
});
