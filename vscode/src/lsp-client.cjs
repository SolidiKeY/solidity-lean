'use strict';
const {EventEmitter}=require('node:events');
const {spawn}=require('node:child_process');
const {join}=require('node:path');
const {pathToFileURL}=require('node:url');
const {RpcPeer,failure,cancellable}=require('./rpc.cjs');
const {checkStartup,serverIdentity,startupError,cancelled,waitForServerVersion}=require('./startup.cjs');
const {processState,groupMembers,running,ownedProcess}=require('./process-state.cjs');
const {incrementalChange}=require('./diagnostic-state.cjs');
const {terminateTree,parseReport}=require('./backend.cjs');
const {trackChild,waitForClose,waitForGroup}=require('./child-lifetime.cjs');

class LanguageClient extends EventEmitter {
  constructor(configuration){
    super();this.configuration=configuration;this.documents=new Map();this.disposed=false;this.ownedProcesses=new Map();
    this.startupAbort=new AbortController();
    this.ready=this.start().catch(error=>{if(this.failure)error=this.failure;else if(this.disposed)error=cancelled();else if(error.code!=='STARTUP')error=startupError('Language server initialization failed: '+error.message,null,error);this.fail(error);throw error;});
    this.ready.catch(()=>{});
  }
  fail(error){if(this.disposed||this.failed)return;if(!this.initialized&&error.code!=='STARTUP')error=startupError('Language server initialization failed: '+error.message,null,error);this.failed=true;this.failure=error;this.emit('serverError',error);this.dispose().catch(()=>{});}
  async start(){
    this.runtimeInfo=await checkStartup(this.configuration,this.startupAbort.signal);if(this.disposed)throw cancelled();
    const configuration=this.configuration;
    this.child=spawn(configuration.nodePath||'node',[join(__dirname,'lsp-server.cjs')],{cwd:configuration.backendPath,
      detached:process.platform!=='win32',windowsHide:true,stdio:['pipe','pipe','pipe']});
    this.child.ownedGroup=process.platform!=='win32';trackChild(this.child);
    this.stderr='';this.child.stderr.on('data',chunk=>{this.stderr=(this.stderr+chunk).slice(-12000);});
    this.peer=new RpcPeer(this.child.stdout,this.child.stdin);
    this.closed=new Promise(resolve=>this.child.once('close',()=>{this.childClosureConfirmed=true;resolve();}));
    this.child.on('error',error=>this.peer.close(error));
    this.child.on('exit',code=>this.peer.close(new Error(`Solidity language server exited ${code}: ${this.stderr}`)));
    this.peer.on('close',error=>this.fail(error));
    for(const [method,event]of [['textDocument/publishDiagnostics','diagnostics'],['solidityLean/report','report'],['solidityLean/status','status'],['solidityLean/invalidated','invalidated']])
      this.peer.onNotification(method,params=>{if(['status','report','invalidated','diagnostics'].includes(event)&&params.synchronizationId!==undefined&&this.documents.get(params.uri)?.synchronizationId!==params.synchronizationId)return;if(event==='report')parseReport(JSON.stringify(params.report));this.emit(event,params);});
    this.peer.onRequest('solidityLean/registerOwnedProcess',params=>{if(this.disposed)return false;if(process.platform!=='linux')return true;const owned=ownedProcess(params,this.child);this.ownedProcesses.set(owned.pid,owned);return true;});
    this.peer.onNotification('solidityLean/ownedProcess',params=>{const owned=this.ownedProcesses.get(params?.pid);if(params?.event==='closed'&&owned?.processBirth===params.birth&&!groupMembers(owned).some(running))this.ownedProcesses.delete(params.pid);});
    this.peer.onNotification('window/logMessage',params=>this.emit('log',params.message));
    this.versionWait=waitForServerVersion(this.peer,this.startupAbort.signal);this.versionWait.promise.catch(error=>this.fail(error));
    const automaticVerification=configuration.automaticVerification||'never';
    const result=await this.peer.request('initialize',{processId:process.pid,rootUri:pathToFileURL(configuration.backendPath).href,
      capabilities:{experimental:{solidityLeanOwnedProcess:true},textDocument:{publishDiagnostics:{versionSupport:true}}},initializationOptions:{backendPath:configuration.backendPath,
        settings:{projectRoot:configuration.projectRoot,includePaths:configuration.includePaths||[],remappings:configuration.remappings||[],workers:configuration.workers||1,timeoutMs:configuration.timeoutMs||600000,automaticVerification,
          counterexamples:!!configuration.counterexamples,auditPreconditions:!!configuration.auditPreconditions}}},{timeoutMs:30000})
    ;
    if(this.disposed)throw cancelled();
    if(!result||!result.capabilities||typeof result.capabilities!=='object'||Array.isArray(result.capabilities))throw startupError('Language server returned invalid initialize capabilities',null);
    this.capabilities=result.capabilities;this.initialized=true;
    const version=this.versionWait.start(result.serverInfo);this.peer.notify('initialized',{});
    const decision=await version;if(this.disposed)throw cancelled();this.serverInfo=decision.serverInfo;this.versionSource=decision.source;
    this.emit('identity',{serverInfo:this.serverInfo,runtimeInfo:this.runtimeInfo,versionSource:this.versionSource});return result;
  }
  async sync(doc,isCurrent=()=>true,signal){
    await cancellable(this.ready,signal);
    if(signal?.aborted)throw failure('Request cancelled',-32800);
    if(this.disposed)throw cancelled();
    if(!isCurrent())throw failure('Language client changed',-32801);
    if(doc.isClosed)throw failure('Document closed',-32801);
    const uri=doc.uri.toString(),text=doc.getText(),previous=this.documents.get(uri);let synchronizationId=previous?.synchronizationId;
    const opened=()=>{this.syncCounter=(this.syncCounter||0)+1;synchronizationId=String(this.syncCounter);this.documents.set(uri,{version:doc.version,text,synchronizationId});this.peer.notify('textDocument/didOpen',{textDocument:{uri,languageId:'solidity',version:doc.version,text,synchronizationId}});};
    if(!previous){opened();}
    else if(previous.version!==doc.version||previous.text!==text){
      if(doc.version<=previous.version){this.peer.notify('textDocument/didClose',{textDocument:{uri}});opened();}
      else this.peer.notify('textDocument/didChange',{textDocument:{uri,version:doc.version},contentChanges:[incrementalChange(previous.text,text)]});
    }
    this.documents.set(uri,{version:doc.version,text,synchronizationId});
  }
  async verify(doc,options={},isCurrent=()=>true){
    try{await this.sync(doc,isCurrent,options.signal);}catch(error){if(options.signal?.aborted||this.disposed||error.code===-32801)error.code='CANCELLED';throw error;}
    let result;
    try{result=await this.peer.request('solidityLean/verify',{textDocument:{uri:doc.uri.toString(),version:doc.version},options:{listing:!!options.listing,
      contract:options.contract,function:options.function,counterexamples:!!options.counterexamples,auditPreconditions:!!options.auditPreconditions,timeoutMs:options.timeoutMs}},
    {signal:options.signal,timeoutMs:options.timeoutMs||600000});}
    catch(error){if([-32800,-32801].includes(error.code))error.code='CANCELLED';throw error;}
    if(!isCurrent()||this.disposed||doc.isClosed)throw cancelled();
    return parseReport(JSON.stringify(result));
  }
  async request(method,doc,params={},options={},isCurrent=()=>true){
    const version=doc.version,text=doc.getText();await this.sync(doc,isCurrent,options.signal);
    const current=()=>isCurrent()&&!this.disposed&&!doc.isClosed&&doc.version===version&&doc.getText()===text;
    if(!current())throw failure('Document content changed',-32801);
    const result=await this.peer.request(method,{textDocument:{uri:doc.uri.toString(),version},...params},options);
    if(!current())throw failure('Document content changed',-32801);return result;
  }
  closeDocument(uri){if(this.peer&&!this.peer.closed&&this.documents.has(uri)){this.peer.notify('textDocument/didClose',{textDocument:{uri}});this.documents.delete(uri);}}
  cancel(uri){if(this.peer&&!this.peer.closed)this.peer.request('solidityLean/cancel',uri?{uri}:{},{timeoutMs:5000}).catch(()=>{});}
  dispose(){
    if(this.disposal)return this.disposal;this.disposed=true;this.startupAbort.abort();return this.disposal=this.finishDispose();
  }
  async finishDispose(){
    if(!this.child){await this.ready.catch(()=>{});this.peer?.close();return;}
    try{if(!this.peer.closed){await this.peer.request('shutdown',null,{timeoutMs:3000});this.peer.notify('exit',null);}}catch{}
    const deadline=Date.now()+1000;try{if(this.peer.closed)for(const child of this.ownedProcesses.values())await waitForGroup(child,{deadline,kill:true});await waitForClose(this.child,{closed:this.closed,kill:this.peer.closed,deadline});for(const child of this.ownedProcesses.values())await waitForGroup(child,{deadline});this.ownedProcesses.clear();}catch(error){for(const child of this.ownedProcesses.values())try{terminateTree(child);}catch{}terminateTree(this.child);throw error;}finally{this.peer.close();}
  }
  resourcesQuiescent(){try{return this.childClosureConfirmed&&!groupMembers(this.child).some(running)&&![...this.ownedProcesses.values()].some(child=>groupMembers(child).some(running));}catch{return false;}}
}

/** Resource configurations get separate servers, so one folder's compiler,
 * proof options or executable can never leak into another folder's requests. */
class LanguageServers extends EventEmitter {
  constructor(configuration){super();this.configuration=configuration;this.clients=new Map();this.owners=new Map();this.retiring=new Set();this.disposed=false;this.reportedErrors=new WeakSet();this.revision=0;this.epochs=new Map();this.retirementKeys=new Map();this.retirementFailures=[];}
  touch(uri){this.epochs.set(uri,(this.epochs.get(uri)||0)+1);this.revision++;}
  ownership(doc,client){const uri=doc.uri.toString(),epoch=this.epochs.get(uri);return()=>!this.disposed&&this.owners.get(uri)===client&&this.epochs.get(uri)===epoch;}
  client(doc){
    if(this.disposed)throw new Error('Language servers disposed');
    if(doc.isClosed)throw failure('Document closed',-32801);
    const configuration=this.configuration(doc),key=JSON.stringify(configuration);
    if(this.restarting||this.retirementKeys.has(key))throw failure('Previous language server is still retiring',-32801);
    let client=this.clients.get(key);
    if(!client||client.failed||client.peer?.closed){
      client=new LanguageClient(configuration);this.clients.set(key,client);
      for(const event of ['report','status','diagnostics','invalidated'])client.on(event,params=>{
        if(this.owners.get(params.uri)===client)this.emit(event,params);
      });
      client.on('serverError',error=>{
        const current=this.clients.get(key)===client;
        const uris=[...this.owners].filter(([,owner])=>owner===client).map(([uri])=>uri);
        Object.assign(error,{uris});this.reportedErrors.add(error);
        for(const uri of uris){this.owners.delete(uri);this.touch(uri);}
        if(this.clients.get(key)===client)this.clients.delete(key);
        this.retire(key,client);
        if(current&&uris.length&&!this.disposed){this.reportedErrors.add(error);this.emit('serverError',Object.assign(error,{uris}));}
      });client.on('log',message=>this.emit('log',message));
      client.on('identity',identity=>{const uris=[...this.owners].filter(([,owner])=>owner===client).map(([uri])=>uri);if(!this.disposed&&this.clients.get(key)===client&&uris.length)this.emit('identity',{...identity,uris});});
    }
    const uri=doc.uri.toString(),previous=this.owners.get(uri);
    if(previous&&previous!==client)previous.closeDocument(uri);
    if(previous!==client)this.touch(uri);this.owners.set(uri,client);return client;
  }
  retire(key,client){
    const retirement=(async()=>{await client.dispose();if(client.child)await waitForClose(client.child,{closed:client.closed});})();
    this.retirementKeys.set(key,retirement);this.retiring.add(retirement);
    const release=()=>{if(this.retirementKeys.get(key)===retirement)this.retirementKeys.delete(key);};
    retirement.then(()=>{this.retiring.delete(retirement);release();},error=>{this.retiring.delete(retirement);this.retirementFailures.push(error);this.emit('log','Failed server cleanup: '+error.message);if(client.resourcesQuiescent?.())release();else client.closed?.then(()=>{if(client.resourcesQuiescent?.())release();});});return retirement;
  }
  async settled(signal,doc){while(this.restarting)await cancellable(this.restarting,signal);if(doc){const key=JSON.stringify(this.configuration(doc));while(this.retirementKeys.has(key))await cancellable(this.retirementKeys.get(key),signal);}if(signal?.aborted)throw failure('Request cancelled',-32800);}
  async open(doc){await this.settled(undefined,doc);const client=this.client(doc),current=this.ownership(doc,client);await client.sync(doc,current);if(!current()||client.disposed)throw failure('Language client changed',-32801);this.emit('identity',{serverInfo:client.serverInfo,runtimeInfo:client.runtimeInfo,uris:[doc.uri.toString()]});return client;}
  async verify(args){await this.settled(args.signal,args.document);const client=this.client(args.document);return client.verify(args.document,args,this.ownership(args.document,client));}
  async request(method,doc,params,options){
    const version=doc.version,text=doc.getText(),sourceCurrent=()=>!doc.isClosed&&doc.version===version&&doc.getText()===text;
    const validate=()=>{if(options?.signal?.aborted)throw failure('Request cancelled',-32800);if(!sourceCurrent())throw failure('Document content changed',-32801);};
    await this.settled(options?.signal,doc);validate();
    const client=this.client(doc),owned=this.ownership(doc,client),current=()=>owned()&&sourceCurrent();
    const result=await client.request(method,doc,params,options,current);validate();if(!current())throw failure('Language client changed',-32801);return result;
  }
  async workspaceSymbols(query,options){await this.settled(options?.signal);const revision=this.revision;const current=()=>!this.disposed&&this.revision===revision;const results=(await Promise.all([...this.clients.values()].map(async client=>{await cancellable(client.ready,options?.signal);if(!current())throw failure('Language clients changed',-32801);return client.peer.request('workspace/symbol',{query},options);}))).flat();if(options?.signal?.aborted)throw failure('Request cancelled',-32800);if(!current())throw failure('Language clients changed',-32801);return [...new Map(results.map(s=>[JSON.stringify(s.location),s])).values()];}
  changed(uri){for(const [key,client]of this.clients)if(!client.peer?.closed)client.ready.then(()=>{if(this.clients.get(key)===client&&!client.disposed)client.peer.notify('workspace/didChangeWatchedFiles',{changes:[{uri:uri.toString(),type:2}]});}).catch(error=>this.operationError(error,[...this.owners].filter(([,owner])=>owner===client).map(([uri])=>uri)));}
  save(doc){const save=async()=>{await this.settled(undefined,doc);const client=this.client(doc),current=this.ownership(doc,client);await client.sync(doc,current);if(!current()||client.disposed||doc.isClosed)throw failure('Language client changed',-32801);client.peer.notify('textDocument/didSave',{textDocument:{uri:doc.uri.toString()},text:doc.getText()});};save().catch(error=>this.operationError(error,[doc.uri.toString()]));}
  operationError(error,uris){if(this.disposed||this.reportedErrors.has(error)||!uris?.length||!uris.some(uri=>this.owners.has(uri)))return;if(![-32800,-32801].includes(error.code)&&error.code!=='CANCELLED'){this.reportedErrors.add(error);this.emit('serverError',Object.assign(error,{uris:error.uris||uris}));}}
  close(uri){const key=uri.toString(),client=this.owners.get(key);client?.closeDocument(key);if(this.owners.delete(key))this.touch(key);}
  cancel(uri){if(uri)this.owners.get(uri.toString())?.cancel(uri.toString());else for(const client of this.clients.values())client.cancel();}
  restart(uris){
    this.revision++;let old;const keys=new Map([...this.clients].map(([key,client])=>[client,key]));
    if(uris){
      const selected=new Set(uris.map(uri=>uri.toString())),candidates=new Set();
      for(const [uri,client]of this.owners)if(selected.has(uri)){client.closeDocument(uri);this.owners.delete(uri);this.touch(uri);candidates.add(client);}
      old=[...candidates].filter(client=>![...this.owners.values()].includes(client));
      for(const [key,client]of this.clients)if(old.includes(client))this.clients.delete(key);
    }else{old=[...this.clients.values()];this.clients.clear();for(const uri of this.owners.keys())this.touch(uri);this.owners.clear();}
    const retirements=old.map(client=>this.retire(keys.get(client),client));
    const operation=(this.restarting||Promise.resolve()).then(async()=>{await Promise.all(retirements);while(this.retiring.size)await Promise.all([...this.retiring]);if(this.retirementFailures.length)throw new AggregateError(this.retirementFailures,'Language server cleanup failed');});
    const pending=operation.finally(()=>{if(this.restarting===pending)this.restarting=null;});
    this.restarting=pending;return pending;
  }
  dispose(){this.disposed=true;this.disposal??=this.restart();return this.disposal;}
}
module.exports={LanguageClient,LanguageServers};
