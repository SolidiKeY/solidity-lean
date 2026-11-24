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
const {trackChild,waitForClose,waitForGroup,enableChildLifetimeObservation}=require('./child-lifetime.cjs');

function documentRequestParams(params,uri,version){
  const captured={...params},target=captured.textDocument;
  if(typeof captured.toJSON==='function'||target!==undefined&&(!target||typeof target!=='object'||Array.isArray(target)||target.uri!==uri||target.version!==undefined&&target.version!==version))throw failure('Request document does not match source',-32801);
  return{...captured,textDocument:{uri,version}};
}

function operationFailure(reason){
  const uris=reason&&typeof reason==='object'?Object.getOwnPropertyDescriptor(reason,'uris'):undefined;
  if(reason instanceof Error&&typeof reason.message==='string'&&Object.isExtensible(reason)&&(!uris||'value'in uris&&uris.writable))return reason;
  const error=new Error(typeof reason?.message==='string'?reason.message:typeof reason==='string'?reason:'Language operation failed',{cause:reason});
  if(reason&&typeof reason==='object')for(const key of Reflect.ownKeys(reason)){
    const descriptor=Object.getOwnPropertyDescriptor(reason,key);
    if(key!=='cause'&&(key!=='message'||typeof descriptor.value==='string')&&'value'in descriptor)Object.defineProperty(error,key,{...descriptor,writable:true,configurable:true});
  }
  return error;
}

function notifyDocument(client,uri,method,params){
  try{client.peer.notify(method,params);}
  catch(error){
    client.documents.delete(uri);
    try{client.peer.close(error instanceof Error?error:Object.assign(failure('Document synchronization failed'),{cause:error}));}
    catch(closeError){client.documentNotificationCloseFailure={method,uri,error:closeError};}
    throw error;
  }
}

class LanguageClient extends EventEmitter {
  constructor(configuration){
    super();this.configuration=configuration;this.documents=new Map();this.disposed=false;this.ownedProcesses=new Map();
    this.startupAbort=new AbortController();
    this.ready=this.start().catch(reason=>{
      let error=this.failure||(this.disposed?cancelled():operationFailure(reason));
      if(!this.failure&&!this.disposed&&error.code!=='STARTUP')error=startupError('Language server initialization failed: '+error.message,null,error);
      this.fail(error);throw this.failure||error;
    });
    this.ready.catch(()=>{});
  }
  fail(error){
    if(this.disposed||this.failed)return;
    error=operationFailure(error);if(!this.initialized&&error.code!=='STARTUP')error=startupError('Language server initialization failed: '+error.message,null,error);
    this.failed=true;this.failure=error;
    try{this.emit('serverError',error);}catch(notificationError){this.failureNotificationFailure={error:notificationError};}
    finally{this.dispose().catch(()=>{});}
  }
  async start(){
    this.runtimeInfo=await checkStartup(this.configuration,this.startupAbort.signal);if(this.disposed)throw cancelled();
    const configuration=this.configuration;
    this.child=spawn(configuration.nodePath||'node',[join(__dirname,'lsp-server.cjs')],{cwd:configuration.backendPath,
      detached:process.platform!=='win32',windowsHide:true,stdio:['pipe','pipe','pipe']});
    this.child.ownedGroup=process.platform!=='win32';if(configuration.diagnosticChildLifetime===true)enableChildLifetimeObservation(this.child);trackChild(this.child);
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
      capabilities:{experimental:{solidityLeanOwnedProcess:true},textDocument:{publishDiagnostics:{versionSupport:true},codeAction:{dataSupport:true,resolveSupport:{properties:['edit']}}}},initializationOptions:{backendPath:configuration.backendPath,
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
    if(this.peer?.closed)throw failure('Connection closed');
    if(!isCurrent())throw failure('Language client changed',-32801);
    if(doc.isClosed)throw failure('Document closed',-32801);
    const uri=doc.uri.toString(),text=doc.getText(),previous=this.documents.get(uri);let synchronizationId=previous?.synchronizationId;
    const opened=()=>{this.syncCounter=(this.syncCounter||0)+1;synchronizationId=String(this.syncCounter);this.documents.set(uri,{version:doc.version,text,synchronizationId});notifyDocument(this,uri,'textDocument/didOpen',{textDocument:{uri,languageId:'solidity',version:doc.version,text,synchronizationId}});};
    if(!previous){opened();}
    else if(previous.version!==doc.version||previous.text!==text){
      if(doc.version<=previous.version){notifyDocument(this,uri,'textDocument/didClose',{textDocument:{uri}});opened();}
      else notifyDocument(this,uri,'textDocument/didChange',{textDocument:{uri,version:doc.version},contentChanges:[incrementalChange(previous.text,text)]});
    }
    this.documents.set(uri,{version:doc.version,text,synchronizationId});
  }
  async verify(doc,options={},isCurrent=()=>true){
    const uri=doc.uri.toString(),version=doc.version,text=doc.getText(),current=()=>isCurrent()&&!doc.isClosed&&doc.uri.toString()===uri&&doc.version===version&&doc.getText()===text;
    try{await this.sync(doc,current,options.signal);}catch(error){if(options.signal?.aborted||this.disposed||error.code===-32801)error.code='CANCELLED';throw error;}
    if(!current()||this.disposed)throw cancelled();
    let result;
    try{result=await this.peer.request('solidityLean/verify',{textDocument:{uri,version},options:{listing:!!options.listing,
      contract:options.contract,function:options.function,counterexamples:!!options.counterexamples,auditPreconditions:!!options.auditPreconditions,timeoutMs:options.timeoutMs}},
    {signal:options.signal,timeoutMs:options.timeoutMs||600000});}
    catch(error){if([-32800,-32801].includes(error.code))error.code='CANCELLED';throw error;}
    if(!current()||this.disposed)throw cancelled();
    return parseReport(JSON.stringify(result));
  }
  async request(method,doc,params={},options={},isCurrent=()=>true){
    if(options?.signal?.aborted)throw failure('Request cancelled',-32800);
    if(doc.isClosed)throw failure('Document closed',-32801);
    const uri=doc.uri.toString(),version=doc.version,text=doc.getText(),requestParams=documentRequestParams(params,uri,version);
    const current=()=>isCurrent()&&!this.disposed&&!doc.isClosed&&doc.uri.toString()===uri&&doc.version===version&&doc.getText()===text;
    await this.sync(doc,current,options.signal);
    if(!current())throw failure('Document content changed',-32801);
    const result=await this.peer.request(method,requestParams,options);
    if(!current())throw failure('Document content changed',-32801);return result;
  }
  closeDocument(uri){if(this.peer&&!this.peer.closed&&this.documents.has(uri)){notifyDocument(this,uri,'textDocument/didClose',{textDocument:{uri}});this.documents.delete(uri);}}
  cancel(uri){if(this.peer&&!this.peer.closed)this.peer.request('solidityLean/cancel',uri?{uri}:{},{timeoutMs:5000}).catch(()=>{});}
  dispose(){
    if(this.disposal)return this.disposal;this.disposed=true;this.startupAbort.abort();return this.disposal=this.finishDispose();
  }
  async finishDispose(){
    if(!this.child){await this.ready.catch(()=>{});this.peer?.close();return;}
    // Diagnostics for a failed retirement: how the shutdown request ended.
    const shutdownStart=Date.now();let shutdownOutcome='peer already closed';
    try{if(!this.peer.closed){shutdownOutcome='pending';await this.peer.request('shutdown',null,{timeoutMs:3000});shutdownOutcome='replied';this.peer.notify('exit',null);}}catch(error){shutdownOutcome='failed: '+error.message;}
    const shutdownMs=Date.now()-shutdownStart;
    const deadline=Date.now()+1000;try{if(this.peer.closed)for(const child of this.ownedProcesses.values())await waitForGroup(child,{deadline,kill:true});await waitForClose(this.child,{closed:this.closed,kill:this.peer.closed,deadline});for(const child of this.ownedProcesses.values())await waitForGroup(child,{deadline});this.ownedProcesses.clear();}catch(error){for(const child of this.ownedProcesses.values())try{terminateTree(child);}catch{}terminateTree(this.child);error.message+=` [shutdown request ${shutdownOutcome} after ${shutdownMs} ms; server stderr tail: ${JSON.stringify(String(this.stderr||'').slice(-600))}]`;throw error;}finally{this.peer.close();}
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
  async verify(args){
    const doc=args.document,uri=doc.uri.toString(),version=doc.version,text=doc.getText(),epoch=this.epochs.get(uri);
    const sourceCurrent=()=>!this.disposed&&!doc.isClosed&&doc.uri.toString()===uri&&doc.version===version&&doc.getText()===text;
    await this.settled(args.signal,doc);if(!sourceCurrent()||this.epochs.get(uri)!==epoch)throw cancelled();
    const client=this.client(doc),owned=this.ownership(doc,client),current=()=>owned()&&sourceCurrent();
    const result=await client.verify(doc,args,current);if(!current())throw cancelled();return result;
  }
  async request(method,doc,params,options){
    if(options?.signal?.aborted)throw failure('Request cancelled',-32800);
    if(doc.isClosed)throw failure('Document closed',-32801);
    const uri=doc.uri.toString(),version=doc.version,text=doc.getText(),epoch=this.epochs.get(uri),sourceCurrent=()=>!doc.isClosed&&doc.uri.toString()===uri&&doc.version===version&&doc.getText()===text;
    const requestParams=documentRequestParams(params,uri,version);
    const validate=()=>{if(options?.signal?.aborted)throw failure('Request cancelled',-32800);if(!sourceCurrent())throw failure('Document content changed',-32801);};
    await this.settled(options?.signal,doc);validate();if(this.epochs.get(uri)!==epoch)throw failure('Language client changed',-32801);
    const client=this.client(doc),owned=this.ownership(doc,client),current=()=>owned()&&sourceCurrent();
    const result=await client.request(method,doc,requestParams,options,current);validate();if(!current())throw failure('Language client changed',-32801);return result;
  }
  async workspaceSymbols(query,options){await this.settled(options?.signal);const revision=this.revision;const current=()=>!this.disposed&&this.revision===revision;const results=(await Promise.all([...this.clients.values()].map(async client=>{await cancellable(client.ready,options?.signal);if(!current())throw failure('Language clients changed',-32801);return client.peer.request('workspace/symbol',{query},options);}))).flat();if(options?.signal?.aborted)throw failure('Request cancelled',-32800);if(!current())throw failure('Language clients changed',-32801);return [...new Map(results.map(s=>[JSON.stringify(s.location),s])).values()];}
  changed(uri){for(const [key,client]of this.clients)if(!client.peer?.closed)client.ready.then(()=>{if(this.clients.get(key)===client&&!client.disposed)client.peer.notify('workspace/didChangeWatchedFiles',{changes:[{uri:uri.toString(),type:2}]});}).catch(error=>this.operationError(error,[...this.owners].filter(([,owner])=>owner===client).map(([uri])=>uri)));}
  save(doc){
    const uri=doc.uri.toString();
    const save=async()=>{
      const version=doc.version,text=doc.getText(),epoch=this.epochs.get(uri),sourceCurrent=()=>!this.disposed&&!doc.isClosed&&doc.uri.toString()===uri&&doc.version===version&&doc.getText()===text;
      await this.settled(undefined,doc);if(!sourceCurrent()||this.epochs.get(uri)!==epoch)throw failure('Saved document changed',-32801);
      const client=this.client(doc),owned=this.ownership(doc,client),current=()=>owned()&&sourceCurrent();await client.sync(doc,current);
      if(!current()||client.disposed)throw failure('Language client changed',-32801);
      notifyDocument(client,uri,'textDocument/didSave',{textDocument:{uri},text});
    };save().catch(error=>this.operationError(error,[uri]));
  }
  operationError(error,uris){
    if(this.disposed||this.reportedErrors.has(error)||!uris?.length||!uris.some(uri=>this.owners.has(uri)))return;
    const code=error?.code;if([-32800,-32801].includes(code)||code==='CANCELLED')return;
    const reported=operationFailure(error);
    Object.defineProperty(reported,'uris',{value:reported.uris||uris,...(Object.hasOwn(reported,'uris')?{}:{writable:true,enumerable:true,configurable:true})});
    if(error!==null&&(typeof error==='object'||typeof error==='function'))this.reportedErrors.add(error);
    this.reportedErrors.add(reported);this.emit('serverError',reported);
  }
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
