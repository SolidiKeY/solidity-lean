#!/usr/bin/env node
'use strict';
const {mkdtempSync,mkdirSync,rmSync}=require('node:fs');
const {join,resolve}=require('node:path');
const {fileURLToPath,pathToFileURL}=require('node:url');
const {createHash}=require('node:crypto');
const {spawn}=require('node:child_process');
const {RpcPeer,failure}=require('./rpc.cjs');
const {WorkerPool,fingerprint}=require('./worker-pool.cjs');
const {terminateTree,parseReport}=require('./backend.cjs');
const model=require('./model.cjs');
const language=require('./language-services.cjs');
const hash=text=>createHash('sha256').update(text).digest('hex');
const defaultSettings={workers:1,timeoutMs:60000,automaticVerification:'never',counterexamples:false,auditPreconditions:false};
const checkVersion=(doc,version)=>{if(!doc||version!==undefined&&doc.version!==version)throw failure('Document content changed',-32801);};
function settings(value={}){
  const result={...defaultSettings,...value};
  if(!Number.isSafeInteger(result.workers)||result.workers<1||result.workers>4)throw failure('workers must be between 1 and 4',-32602);
  if(!Number.isSafeInteger(result.timeoutMs)||result.timeoutMs<1||result.timeoutMs>3600000)throw failure('Invalid verification timeout',-32602);
  if(!['never','change','save'].includes(result.automaticVerification))throw failure('Invalid automaticVerification',-32602);
  return result;
}

class SolidityService {
  constructor(peer,root,configuration={},testing={}){
    this.peer=peer;this.root=resolve(root);this.settings=settings(configuration);this.docs=new Map();this.cache=new Map();this.requests=new Map();this.hits=0;this.misses=0;
    this.fingerprint=testing.fingerprint||(()=>fingerprint(this.root));this.generation=this.fingerprint();this.testing=testing;
    mkdirSync(join(this.root,'.lake'),{recursive:true});this.directory=mkdtempSync(join(this.root,'.lake/editor-lsp-'));
    this.analysisPool=new WorkerPool(this.root,join(this.directory,'analysis'),1);
    this.pool=new WorkerPool(this.root,join(this.directory,'proof'),this.settings.workers);
    this.closed=false;
  }
  notify(method,params){if(!this.closed&&!this.peer.closed)this.peer.notify(method,params);}
  current(doc,version,generation=this.generation){return !this.closed&&this.docs.get(doc.uri)===doc&&doc.version===version&&this.generation===generation;}
  status(doc,state,extra={}){
    const functions=doc.index?.nodes.filter(n=>n.nodeType==='FunctionDefinition').map(n=>({range:doc.index.nameRange(n),status:['queued','running','compiling'].includes(state)?'running':'ready'})).filter(f=>f.range);
    this.notify('solidityLean/status',{uri:doc.uri,version:doc.version,state,functions:state==='cancelled'?[]:functions,...extra});
  }
  diagnostics(doc,diagnostics){this.notify('textDocument/publishDiagnostics',{uri:doc.uri,version:doc.version,diagnostics});}
  cancel(doc){
    if(!doc)return;clearTimeout(doc.timer);doc.analysisAbort?.abort();doc.verifyAbort?.abort();
    // A new verification must never join the compiler promise just cancelled
    // by its preceding cancel request (for example while symbols are loading).
    doc.analysisPromise=null;this.status(doc,'cancelled');
  }
  open(document){
    if(!Number.isSafeInteger(document.version)||typeof document.text!=='string'||Buffer.byteLength(document.text)>8*1024*1024)throw failure('Invalid or oversized document',-32602);
    const path=fileURLToPath(document.uri);if(!path.endsWith('.sol'))throw failure('Only Solidity files are supported',-32602);
    this.cancel(this.docs.get(document.uri));
    const doc={uri:document.uri,path,text:document.text,version:document.version};this.docs.set(doc.uri,doc);this.schedule(doc);return doc;
  }
  change(params){
    const doc=this.docs.get(params.textDocument.uri);if(!doc)throw failure('Document is not open',-32602);
    if(!Number.isSafeInteger(params.textDocument.version)||params.textDocument.version<=doc.version)throw failure('Document version must increase',-32602);
    const text=language.applyChanges(doc.text,params.contentChanges);
    if(Buffer.byteLength(text)>8*1024*1024)throw failure('Document exceeds 8 MiB',-32602);
    this.cancel(doc);Object.assign(doc,{text,version:params.textDocument.version,compiled:null,index:null,analysisPromise:null,verifyPromise:null,report:null});
    this.diagnostics(doc,[]);this.schedule(doc);
  }
  schedule(doc){
    const version=doc.version;
    doc.timer=setTimeout(()=>{
      if(!this.current(doc,version))return;
      const action=this.settings.automaticVerification==='change'?this.verify(doc.uri,{}):this.analyze(doc);
      action.catch(error=>{if(![-32800,-32801].includes(error.code))this.notify('window/logMessage',{type:2,message:error.message});});
    },150);
  }
  save(params){
    const doc=this.docs.get(params.textDocument.uri);if(!doc)return;
    if(params.text!==undefined&&params.text!==doc.text)throw failure('Saved text differs from current document',-32801);
    if(this.settings.automaticVerification==='save')this.verify(doc.uri,{}).catch(()=>{});
  }
  close(uri){const doc=this.docs.get(uri);this.cancel(doc);if(doc)this.diagnostics(doc,[]);this.docs.delete(uri);}
  reset(configuration=this.settings){
    this.buildEpoch=(this.buildEpoch||0)+1;if(this.buildChild){terminateTree(this.buildChild);this.buildChild=null;}
    for(const doc of this.docs.values())this.cancel(doc);
    this.analysisPool.dispose();this.pool.dispose();this.cache.clear();this.settings=settings(configuration);
    this.analysisPool=new WorkerPool(this.root,join(this.directory,'analysis-'+Date.now()),1);
    this.pool=new WorkerPool(this.root,join(this.directory,'proof-'+Date.now()),this.settings.workers);
    this.buildPromise=null;
    for(const doc of this.docs.values())Object.assign(doc,{compiled:null,index:null,analysisPromise:null,verifyPromise:null,report:null});
  }
  refresh(){const next=this.fingerprint();if(next!==this.generation){this.reset();this.generation=next;}}
  async build(){
    if(this.testing.verify)return;
    if(this.buildPromise)return this.buildPromise;
    const epoch=this.buildEpoch||0;
    const operation=(async()=>{
      const {lakeCommand}=await import(pathToFileURL(join(this.root,'scripts/lake-command.mjs')).href);
      if(this.closed||epoch!==(this.buildEpoch||0))throw failure('Backend build cancelled',-32800);
      await new Promise((resolvePromise,reject)=>{
        const child=spawn(lakeCommand(),['build','Solidity.Frontend.Testing'],{cwd:this.root,detached:process.platform!=='win32',stdio:['ignore','pipe','pipe']});
        this.buildChild=child;let log='';const collect=chunk=>{log=(log+chunk).slice(-16000);};child.stdout.on('data',collect);child.stderr.on('data',collect);
        const timer=setTimeout(()=>{terminateTree(child);reject(failure('Backend build timed out',-32800));},this.settings.timeoutMs);
        child.once('error',error=>{clearTimeout(timer);reject(error);});
        child.once('close',code=>{clearTimeout(timer);if(this.buildChild===child)this.buildChild=null;if(code===0)resolvePromise();else reject(new Error('Backend build failed: '+log));});
      });
      if(this.closed||epoch!==(this.buildEpoch||0))throw failure('Backend build cancelled',-32800);
      // A successful build updates artifact identities. Nothing is cached yet.
      this.generation=this.fingerprint();this.cache.clear();
    })();
    const pending=operation.catch(error=>{if(this.buildPromise===pending)this.buildPromise=null;throw error;});
    this.buildPromise=pending;return pending;
  }
  async analyze(doc){
    this.refresh();if(doc.compiled)return doc.compiled;if(doc.analysisPromise)return doc.analysisPromise;
    const version=doc.version,generation=this.generation,text=doc.text,controller=new AbortController();doc.analysisAbort=controller;
    doc.analysisPromise=(async()=>{
      this.status(doc,'compiling');const start=Date.now();
      try{
        const compiled=this.testing.analyze?await this.testing.analyze(doc,controller.signal):await this.analysisPool.run({action:'analyze',source:doc.path,text},{signal:controller.signal,timeoutMs:this.settings.timeoutMs});
        if(!this.current(doc,version,generation)||controller.signal.aborted)throw failure('Document content changed',-32801);
        if(compiled.fixture.header.sourceSha256!==hash(text))throw new Error('Compiler source hash mismatch');
        doc.compiled=compiled;doc.compileMs=Date.now()-start;doc.index=language.index(text,compiled.rawAst);
        const proofDiagnostics=doc.report?model.diagnostics(doc.report).map(d=>({range:d.range,severity:d.severity==='error'?1:2,message:d.message,code:d.code,source:'Solidity Lean'})):[];
        this.diagnostics(doc,[...this.compilerDiagnostics(doc,compiled.diagnostics),...proofDiagnostics]);if(!doc.verifyPromise&&!doc.report)this.status(doc,'ready');return compiled;
      }catch(error){
        if(this.current(doc,version,generation)&&![-32800,-32801].includes(error.code))this.diagnostics(doc,this.compilerDiagnostics(doc,error.diagnostics||[{severity:'error',message:error.message}]));
        throw error;
      }
    })();
    const pending=doc.analysisPromise;
    try{return await pending;}finally{if(doc.analysisPromise===pending)doc.analysisPromise=null;}
  }
  compilerDiagnostics(doc,diagnostics=[]){
    return diagnostics.filter(d=>['error','warning'].includes(d.severity)).map(d=>({range:d.sourceLocation&&d.sourceLocation.start>=0?
      language.byteRange(doc.text,`${d.sourceLocation.start}:${d.sourceLocation.end-d.sourceLocation.start}:0`)||model.rangeOf({}):model.rangeOf({}),
      severity:d.severity==='error'?1:2,source:'solc',code:d.errorCode,message:d.formattedMessage||d.message}));
  }
  publish(doc,report,cacheHit=false,selection={}){
    const full=selection.function&&doc.report?{...report,results:[...doc.report.results.filter(old=>!report.results.some(r=>r.contract===old.contract&&(r.signature||r.function)===(old.signature||old.function))),...report.results]}:report;
    doc.report=full;
    const converted=model.diagnostics(full).map(d=>({range:d.range,severity:d.severity==='error'?1:2,message:d.message,code:d.code,source:'Solidity Lean'}));
    this.diagnostics(doc,[...this.compilerDiagnostics(doc,doc.compiled?.diagnostics),...converted]);
    this.notify('solidityLean/report',{uri:doc.uri,version:doc.version,sourceHash:hash(doc.text),report,cacheHit,selection:{function:selection.function,contract:selection.contract}});
    this.status(doc,'complete',{cacheHit,functions:full.results.map(r=>({range:model.rangeOf(r),status:r.status}))});
  }
  async verify(uri,options={},signal){
    const doc=this.docs.get(uri);checkVersion(doc,options.version);clearTimeout(doc.timer);
    this.refresh();
    const key=JSON.stringify([uri,hash(doc.text),this.generation,!!options.listing,options.contract||'',options.function||'',
      options.counterexamples??this.settings.counterexamples,options.auditPreconditions??this.settings.auditPreconditions]);
    if(doc.verifyPromise&&doc.verifyKey===key&&!doc.verifyAbort?.signal.aborted)return this.wait(doc.verifyPromise,signal);
    doc.verifyAbort?.abort();const controller=new AbortController();doc.verifyAbort=controller;doc.verifyKey=key;
    const abort=()=>controller.abort();signal?.addEventListener('abort',abort,{once:true});if(signal?.aborted)controller.abort();
    const version=doc.version,text=doc.text;
    const pending=(async()=>{
      if(controller.signal.aborted)throw failure('Request cancelled',-32800);
      const cached=this.cache.get(key);
      if(cached){
        const generation=this.generation;
        await this.analyze(doc);
        if(!this.current(doc,version,generation)||doc.verifyAbort!==controller||this.fingerprint()!==generation||controller.signal.aborted)throw failure('Document or backend changed',-32801);
        this.cache.delete(key);this.cache.set(key,cached);this.hits++;this.publish(doc,cached,true,options);return cached;
      }
      this.misses++;this.status(doc,'queued');
      try{
        const compiled=await this.analyze(doc);if(controller.signal.aborted)throw failure('Request cancelled',-32800);await this.wait(this.build(),controller.signal);
        if(!this.current(doc,version)||controller.signal.aborted)throw failure('Request cancelled',-32800);
        const generation=this.generation;this.status(doc,'running');const start=Date.now();
        const task={action:'verify',source:doc.path,text,compiled,options:{...this.settings,...options}};
        const report=this.testing.verify?await this.testing.verify(task,controller.signal):await this.pool.run(task,{signal:controller.signal,timeoutMs:options.timeoutMs||this.settings.timeoutMs});
        if(!this.current(doc,version,generation)||doc.verifyAbort!==controller||this.fingerprint()!==generation||controller.signal.aborted)throw failure('Document or backend changed',-32801);
        parseReport(JSON.stringify(report));
        if(report.results.some(row=>row.source!==doc.path||row.sourceHash!==hash(text)))throw new Error('Verification source identity mismatch');
        if((!task.options.counterexamples||options.listing)&&report.results.some(r=>r.status==='refuted'))throw new Error('Unrequested counterexample evidence');
        if(task.options.auditPreconditions&&!options.listing&&report.results.some(r=>r.preconditions===undefined))throw new Error('Missing requested precondition audit');
        report.timings={compileMs:doc.compileMs,proofMs:Date.now()-start};
        // Recompute the key after the initial build changed artifact identities.
        const storedKey=JSON.stringify([uri,hash(text),generation,!!options.listing,options.contract||'',options.function||'',task.options.counterexamples,task.options.auditPreconditions]);
        this.cache.set(storedKey,report);while(this.cache.size>32)this.cache.delete(this.cache.keys().next().value);
        this.publish(doc,report,false,options);return report;
      }catch(error){
        if(this.current(doc,version)&&doc.verifyAbort===controller)this.status(doc,[-32800,-32801].includes(error.code)?'cancelled':'error',{message:error.message});
        throw error;
      }
    })();
    doc.verifyPromise=pending;
    try{return await pending;}finally{signal?.removeEventListener('abort',abort);if(doc.verifyPromise===pending)doc.verifyPromise=null;}
  }
  wait(promise,signal){
    if(!signal)return promise;if(signal.aborted)return Promise.reject(failure('Request cancelled',-32800));
    return new Promise((resolvePromise,reject)=>{
      const abort=()=>reject(failure('Request cancelled',-32800));signal.addEventListener('abort',abort,{once:true});
      promise.then(resolvePromise,reject).finally(()=>signal.removeEventListener('abort',abort));
    });
  }
  async language(method,params){
    const doc=this.docs.get(params.textDocument.uri);checkVersion(doc,params.textDocument.version);
    const version=doc.version;
    try{await this.analyze(doc);}catch(error){if([-32800,-32801].includes(error.code))throw error;}
    if(!this.current(doc,version))throw failure('Document content changed',-32801);
    if(method==='textDocument/completion')return language.completion(doc.text,params.position,doc.index);
    if(method==='textDocument/documentSymbol')return doc.index?.symbols||[];
    if(method==='textDocument/signatureHelp')return language.signatureHelp(doc.text,params.position,doc.index);
    const occurrence=doc.index?.occurrence(params.position),target=occurrence?.declaration;
    if(method==='textDocument/hover'){
      const rows=doc.report?.results.filter(r=>language.contains(model.rangeOf(r),params.position));
      const row=rows?.find(r=>r.sourceId>=0)||rows?.[0];
      if(row)return {contents:{kind:'plaintext',value:model.detail(row)},range:model.rangeOf(row)};
      if(!target)return null;
      return {contents:{kind:'plaintext',value:`${target.name||target.kind}: ${target.typeDescriptions?.typeString||target.nodeType}`},range:occurrence.range};
    }
    if(!target)return method==='textDocument/references'||method==='textDocument/documentHighlight'?[]:null;
    if(method==='textDocument/definition')return {uri:doc.uri,range:doc.index.nameRange(target)};
    const ranges=doc.index.references(target,params.context?.includeDeclaration??true);
    if(method==='textDocument/references')return ranges.map(range=>({uri:doc.uri,range}));
    if(method==='textDocument/documentHighlight')return ranges.map(range=>({range,kind:1}));
    if(method==='textDocument/prepareRename')return {range:occurrence.range,placeholder:target.name};
    if(method==='textDocument/rename'){
      if(!language.validIdentifier(params.newName))throw failure('Invalid Solidity identifier',-32602);
      if([...doc.index.declarations.values()].some(n=>n.id!==target.id&&n.name===params.newName))throw failure('Rename would collide with an existing declaration',-32602);
      const escaped=(target.name||'').replace(/[.*+?^${}()|[\]\\]/g,'\\$&');
      if(doc.index.nodes.some(n=>typeof n.documentation?.text==='string'&&new RegExp(`(?<![\\w$])${escaped}(?![\\w$])`).test(n.documentation.text)))throw failure('Rename involving specification text requires a manual specification update',-32602);
      return {documentChanges:[{textDocument:{uri:doc.uri,version},edits:ranges.map(range=>({range,newText:params.newName}))}]};
    }
    return null;
  }
  dispose(){
    if(this.closed)return;
    for(const doc of this.docs.values())this.cancel(doc);
    this.closed=true;this.pool.dispose();this.analysisPool.dispose();if(this.buildChild)terminateTree(this.buildChild);
    rmSync(this.directory,{recursive:true,force:true});
  }
}

function startServer(input=process.stdin,output=process.stdout){
  const peer=new RpcPeer(input,output);let service,shuttingDown=false;
  peer.on('handlerError',error=>{if(!peer.closed)peer.notify('window/logMessage',{type:1,message:error.message});});
  peer.onRequest('initialize',params=>{
    if(service)throw failure('Already initialized',-32600);
    service=new SolidityService(peer,params.initializationOptions?.backendPath||fileURLToPath(params.rootUri),params.initializationOptions?.settings);
    return {serverInfo:{name:'Solidity Lean Language Server',version:'0.4.0'},capabilities:{textDocumentSync:{openClose:true,change:2,save:{includeText:true}},hoverProvider:true,
      completionProvider:{triggerCharacters:['.']},definitionProvider:true,referencesProvider:true,documentSymbolProvider:true,documentHighlightProvider:true,
      renameProvider:{prepareProvider:true},signatureHelpProvider:{triggerCharacters:['(',',']}}};
  });
  const ready=()=>{if(!service||shuttingDown)throw failure('Server is not initialized',-32002);return service;};
  peer.onNotification('initialized',()=>{});
  peer.onNotification('textDocument/didOpen',params=>ready().open(params.textDocument));
  peer.onNotification('textDocument/didChange',params=>ready().change(params));
  peer.onNotification('textDocument/didSave',params=>ready().save(params));
  peer.onNotification('textDocument/didClose',params=>ready().close(params.textDocument.uri));
  peer.onNotification('workspace/didChangeConfiguration',params=>{const s=ready();s.reset(params.settings);});
  peer.onNotification('$/cancelRequest',params=>service?.requests.get(params.id)?.abort());
  peer.onRequest('solidityLean/verify',async(params,id)=>{
    const s=ready(),controller=new AbortController();s.requests.set(id,controller);
    try{return await s.verify(params.textDocument.uri,{...params.options,version:params.textDocument.version},controller.signal);}
    finally{s.requests.delete(id);}
  });
  peer.onRequest('solidityLean/cancel',params=>{
    const s=ready();if(params?.uri)s.cancel(s.docs.get(params.uri));else for(const doc of s.docs.values())s.cancel(doc);return true;
  });
  peer.onRequest('solidityLean/stats',()=>({pid:process.pid,documents:service.docs.size,cacheHits:service.hits,cacheMisses:service.misses,
    workers:service.pool.workers.map(w=>w.child.pid),queued:service.pool.queue.length,generation:service.generation}));
  for(const method of ['hover','completion','definition','references','documentSymbol','signatureHelp','documentHighlight','prepareRename','rename'])
    peer.onRequest('textDocument/'+method,params=>ready().language('textDocument/'+method,params));
  peer.onRequest('shutdown',()=>{shuttingDown=true;service?.dispose();return null;});
  peer.onNotification('exit',()=>{service?.dispose();process.exit(shuttingDown?0:1);});
  peer.on('close',()=>{service?.dispose();if(input===process.stdin)process.exit(shuttingDown?0:1);});
  for(const signal of ['SIGINT','SIGTERM'])process.once(signal,()=>{service?.dispose();process.exit(0);});
  return {peer,get service(){return service;}};
}
module.exports={SolidityService,startServer,settings};
if(require.main===module)startServer();
