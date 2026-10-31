'use strict';
const {EventEmitter}=require('node:events');
const {spawn}=require('node:child_process');
const {join}=require('node:path');
const {pathToFileURL}=require('node:url');
const {RpcPeer,failure}=require('./rpc.cjs');
const {terminateTree,parseReport}=require('./backend.cjs');

class LanguageClient extends EventEmitter {
  constructor(configuration){
    super();this.configuration=configuration;this.documents=new Map();this.disposed=false;
    this.child=spawn(configuration.nodePath||'node',[join(__dirname,'lsp-server.cjs')],{cwd:configuration.backendPath,
      detached:process.platform!=='win32',windowsHide:true,stdio:['pipe','pipe','pipe']});
    this.stderr='';this.child.stderr.on('data',chunk=>{this.stderr=(this.stderr+chunk).slice(-12000);});
    this.peer=new RpcPeer(this.child.stdout,this.child.stdin);
    this.closed=new Promise(resolve=>this.child.once('close',resolve));
    this.child.on('error',error=>this.peer.close(error));
    this.child.on('exit',code=>this.peer.close(new Error(`Solidity language server exited ${code}: ${this.stderr}`)));
    this.peer.on('close',error=>{if(!this.disposed)this.emit('serverError',error);});
    for(const [method,event]of [['textDocument/publishDiagnostics','diagnostics'],['solidityLean/report','report'],['solidityLean/status','status']])
      this.peer.onNotification(method,params=>{if(event==='report')parseReport(JSON.stringify(params.report));this.emit(event,params);});
    this.peer.onNotification('window/logMessage',params=>this.emit('log',params.message));
    const automaticVerification=configuration.automaticVerification||'never';
    this.ready=this.peer.request('initialize',{processId:process.pid,rootUri:pathToFileURL(configuration.backendPath).href,
      capabilities:{textDocument:{publishDiagnostics:{versionSupport:true}}},initializationOptions:{backendPath:configuration.backendPath,
        settings:{workers:configuration.workers||1,timeoutMs:configuration.timeoutMs||600000,automaticVerification,
          counterexamples:!!configuration.counterexamples,auditPreconditions:!!configuration.auditPreconditions}}},{timeoutMs:30000})
      .then(result=>{this.capabilities=result.capabilities;this.peer.notify('initialized',{});return result;});
    // Initialization can fail before a provider/verification awaits it.
    this.ready.catch(error=>{if(!this.disposed)this.emit('serverError',error);});
  }
  async sync(doc){
    await this.ready;
    if(doc.isClosed)throw failure('Document closed',-32801);
    const uri=doc.uri.toString(),text=doc.getText(),previous=this.documents.get(uri);
    if(!previous){this.peer.notify('textDocument/didOpen',{textDocument:{uri,languageId:'solidity',version:doc.version,text}});}
    else if(previous.version!==doc.version||previous.text!==text){
      if(doc.version<=previous.version){this.peer.notify('textDocument/didClose',{textDocument:{uri}});this.peer.notify('textDocument/didOpen',{textDocument:{uri,languageId:'solidity',version:doc.version,text}});}
      else this.peer.notify('textDocument/didChange',{textDocument:{uri,version:doc.version},contentChanges:[{text}]});
    }
    this.documents.set(uri,{version:doc.version,text});
  }
  async verify(doc,options={}){
    try{await this.sync(doc);}catch(error){if(options.signal?.aborted||this.disposed||error.code===-32801)error.code='CANCELLED';throw error;}
    let result;
    try{result=await this.peer.request('solidityLean/verify',{textDocument:{uri:doc.uri.toString(),version:doc.version},options:{listing:!!options.listing,
      contract:options.contract,function:options.function,counterexamples:!!options.counterexamples,auditPreconditions:!!options.auditPreconditions,timeoutMs:options.timeoutMs}},
    {signal:options.signal,timeoutMs:options.timeoutMs||600000});}
    catch(error){if([-32800,-32801].includes(error.code))error.code='CANCELLED';throw error;}
    return parseReport(JSON.stringify(result));
  }
  async request(method,doc,params={},options={}){
    const version=doc.version,text=doc.getText();await this.sync(doc);
    const current=()=>!doc.isClosed&&doc.version===version&&doc.getText()===text;
    if(!current())throw failure('Document content changed',-32801);
    const result=await this.peer.request(method,{textDocument:{uri:doc.uri.toString(),version},...params},options);
    if(!current())throw failure('Document content changed',-32801);return result;
  }
  closeDocument(uri){if(!this.peer.closed&&this.documents.has(uri)){this.peer.notify('textDocument/didClose',{textDocument:{uri}});this.documents.delete(uri);}}
  cancel(uri){if(!this.peer.closed)this.peer.request('solidityLean/cancel',uri?{uri}:{},{timeoutMs:5000}).catch(()=>{});}
  async dispose(){
    if(this.disposed)return;this.disposed=true;
    try{if(!this.peer.closed){await this.peer.request('shutdown',null,{timeoutMs:3000});this.peer.notify('exit',null);}}catch{}
    let timer;await Promise.race([this.closed,new Promise(resolve=>{timer=setTimeout(()=>{terminateTree(this.child);resolve();},1000);})]);clearTimeout(timer);this.peer.close();
  }
}

/** Resource configurations get separate servers, so one folder's compiler,
 * proof options or executable can never leak into another folder's requests. */
class LanguageServers extends EventEmitter {
  constructor(configuration){super();this.configuration=configuration;this.clients=new Map();this.owners=new Map();this.disposed=false;}
  client(doc){
    if(this.disposed)throw new Error('Language servers disposed');
    if(doc.isClosed)throw failure('Document closed',-32801);
    const configuration=this.configuration(doc),key=JSON.stringify(configuration);
    let client=this.clients.get(key);
    if(!client||client.peer.closed){
      client=new LanguageClient(configuration);this.clients.set(key,client);
      for(const event of ['report','status','diagnostics'])client.on(event,params=>{
        if(this.owners.get(params.uri)===client)this.emit(event,params);
      });
      client.on('serverError',error=>this.emit('serverError',error));client.on('log',message=>this.emit('log',message));
    }
    const uri=doc.uri.toString(),previous=this.owners.get(uri);
    if(previous&&previous!==client)previous.closeDocument(uri);
    this.owners.set(uri,client);return client;
  }
  async settled(){while(this.restarting)await this.restarting;}
  async open(doc){await this.settled();const client=this.client(doc);await client.sync(doc);return client;}
  async verify(args){await this.settled();const client=this.client(args.document);return client.verify(args.document,args);}
  async request(method,doc,params,options){await this.settled();const client=this.client(doc);return client.request(method,doc,params,options);}
  save(doc){this.open(doc).then(client=>client.peer.notify('textDocument/didSave',{textDocument:{uri:doc.uri.toString()},text:doc.getText()})).catch(error=>this.emit('serverError',error));}
  close(uri){const key=uri.toString(),client=this.owners.get(key);client?.closeDocument(key);this.owners.delete(key);}
  cancel(uri){if(uri)this.owners.get(uri.toString())?.cancel(uri.toString());else for(const client of this.clients.values())client.cancel();}
  restart(){
    const old=[...this.clients.values()];this.clients.clear();this.owners.clear();
    const operation=(this.restarting||Promise.resolve()).then(()=>Promise.all(old.map(client=>client.dispose())));
    const pending=operation.finally(()=>{if(this.restarting===pending)this.restarting=null;});
    this.restarting=pending;return pending;
  }
  dispose(){this.disposed=true;this.disposal??=this.restart();return this.disposal;}
}
module.exports={LanguageClient,LanguageServers};
