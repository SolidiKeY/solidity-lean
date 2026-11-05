'use strict';
const {EventEmitter}=require('node:events');

class LspFrames extends EventEmitter {
  constructor(limit=32*1024*1024){super();this.limit=limit;this.buffer=Buffer.alloc(0);}
  push(chunk){
    this.buffer=Buffer.concat([this.buffer,chunk]);
    while(this.buffer.length){
      const end=this.buffer.indexOf('\r\n\r\n');
      if(end<0){if(this.buffer.length>8192)throw new Error('Oversize LSP header');return;}
      const lengths=[...this.buffer.subarray(0,end).toString('ascii').matchAll(/^Content-Length:\s*(\d+)\s*$/gim)];
      if(lengths.length!==1)throw new Error('Invalid LSP Content-Length');
      const length=Number(lengths[0][1]);
      if(!Number.isSafeInteger(length)||length>this.limit)throw new Error('Oversize LSP body');
      if(this.buffer.length<end+4+length)return;
      const body=this.buffer.subarray(end+4,end+4+length);this.buffer=this.buffer.subarray(end+4+length);
      this.emit('message',JSON.parse(body.toString('utf8')));
    }
  }
  end(){if(this.buffer.length)throw new Error('Truncated LSP frame');}
}
const failure=(message,code=-32603)=>Object.assign(new Error(message),{code});

/** Full-duplex JSON-RPC over LSP byte framing. Notifications are synchronous
 * until their handler first awaits, preserving document-event ordering. */
class RpcPeer extends EventEmitter {
  constructor(input,output){
    super();this.output=output;this.next=0;this.pending=new Map();this.requests=new Map();this.notifications=new Map();this.closed=false;
    this.frames=new LspFrames();
    this.frames.on('message',message=>this.receive(message));
    input.on('data',chunk=>{try{this.frames.push(chunk);}catch(error){this.close(error);}});
    input.on('end',()=>{try{this.frames.end();}catch(error){this.close(error);return;}this.close(failure('Connection closed'));});
    input.on('error',error=>this.close(error));output.on('error',error=>this.close(error));
  }
  write(message){
    if(this.closed)throw failure('Connection closed');
    const body=Buffer.from(JSON.stringify(message));
    this.output.write(Buffer.concat([Buffer.from(`Content-Length: ${body.length}\r\n\r\n`),body]));
  }
  notify(method,params){this.write({jsonrpc:'2.0',method,params});}
  request(method,params,{signal,timeoutMs=60000}={}){
    if(signal?.aborted)return Promise.reject(failure('Request cancelled',-32800));
    const id=++this.next;
    return new Promise((resolve,reject)=>{
      const finish=(error,result)=>{
        if(!this.pending.delete(id))return;
        clearTimeout(timer);signal?.removeEventListener('abort',abort);
        if(error)reject(error);else resolve(result);
      };
      const abort=()=>{if(!this.closed)this.notify('$/cancelRequest',{id});finish(failure('Request cancelled',-32800));};
      const timer=setTimeout(()=>{if(!this.closed)this.notify('$/cancelRequest',{id});finish(failure('Request timed out',-32800));},timeoutMs);
      this.pending.set(id,{finish});signal?.addEventListener('abort',abort,{once:true});
      try{this.write({jsonrpc:'2.0',id,method,params});}catch(error){finish(error);}
    });
  }
  receive(message){
    if(this.closed)return;
    if(message.jsonrpc!=='2.0')return;
    if(message.method===undefined){
      const pending=this.pending.get(message.id);
      if(pending)pending.finish(message.error?Object.assign(new Error(message.error.message),{code:message.error.code,data:message.error.data}):null,message.result);
      return;
    }
    if(message.id===undefined){
      try{Promise.resolve(this.notifications.get(message.method)?.(message.params)).catch(error=>this.emit('handlerError',error));}
      catch(error){this.emit('handlerError',error);}return;
    }
    const handler=this.requests.get(message.method);
    let result;
    try{if(!handler)throw failure('Method not found: '+message.method,-32601);result=handler(message.params,message.id);}
    catch(error){result=Promise.reject(error);}
    Promise.resolve(result)
      .then(result=>{if(!this.closed)this.write({jsonrpc:'2.0',id:message.id,result:result??null});},error=>{
        if(!this.closed)this.write({jsonrpc:'2.0',id:message.id,error:{code:Number.isInteger(error.code)?error.code:-32603,message:error.message,data:error.data}});
      });
  }
  onRequest(method,handler){this.requests.set(method,handler);}
  onNotification(method,handler){this.notifications.set(method,handler);}
  close(error=failure('Connection closed')){
    if(this.closed)return;this.closed=true;
    for(const pending of [...this.pending.values()])pending.finish(error);
    this.emit('close',error);
  }
}
module.exports={LspFrames,RpcPeer,failure};
