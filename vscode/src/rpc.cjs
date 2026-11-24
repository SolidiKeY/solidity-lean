'use strict';
const {EventEmitter}=require('node:events');

const {LspFrames}=require('./lsp-frames.cjs');

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
      const finish=(settle,value)=>{
        if(!this.pending.delete(id))return;
        clearTimeout(timer);signal?.removeEventListener('abort',abort);
        settle(value);
      };
      const succeed=value=>finish(resolve,value),fail=error=>finish(reject,error);
      const cancel=message=>{let writeFailed=false,writeError;try{if(!this.closed)this.notify('$/cancelRequest',{id});}catch(error){writeFailed=true;writeError=error;}fail(failure(message,-32800));if(writeFailed)this.close(writeError);};
      const abort=()=>cancel('Request cancelled');
      const timer=setTimeout(()=>cancel('Request timed out'),timeoutMs);
      this.pending.set(id,{resolve:succeed,reject:fail});signal?.addEventListener('abort',abort,{once:true});
      try{this.write({jsonrpc:'2.0',id,method,params});}catch(error){fail(error);}
    });
  }
  receive(message){
    if(this.closed)return;
    if(message.jsonrpc!=='2.0')return;
    if(message.method===undefined){
      const pending=this.pending.get(message.id);
      if(pending){
        const hasResult=Object.hasOwn(message,'result'),hasError=Object.hasOwn(message,'error'),error=message.error;
        if(hasResult===hasError||hasError&&(!error||typeof error!=='object'||Array.isArray(error)||!Number.isInteger(error.code)||typeof error.message!=='string')){
          this.close(failure('Malformed JSON-RPC response',-32600));return;
        }
        if(hasError)pending.reject(Object.assign(new Error(error.message),{code:error.code,data:error.data}));
        else pending.resolve(message.result);
      }
      return;
    }
    if(typeof message.method!=='string'||message.id!==undefined&&!(typeof message.id==='string'||typeof message.id==='number'&&Number.isFinite(message.id))){
      this.close(failure('Malformed JSON-RPC request',-32600));return;
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
  onNotification(method,handler){this.notifications.set(method,handler);return{dispose:()=>{if(this.notifications.get(method)===handler)this.notifications.delete(method);}};}
  close(error=failure('Connection closed')){
    if(this.closed)return;this.closed=true;
    for(const pending of [...this.pending.values()])pending.reject(error);
    this.notifications.clear();this.requests.clear();
    this.emit('close',error);
  }
}
function cancellable(promise,signal){
  if(!signal)return promise;
  return new Promise((resolve,reject)=>{
    let settled=false;
    const finish=(settle,value)=>{if(settled)return;settled=true;signal.removeEventListener('abort',abort);settle(value);};
    const abort=()=>finish(reject,failure('Request cancelled',-32800));
    signal.addEventListener('abort',abort,{once:true});
    Promise.resolve(promise).then(value=>finish(resolve,value),error=>finish(reject,error));
    if(signal.aborted)abort();
  });
}
module.exports={LspFrames,RpcPeer,failure,cancellable};
