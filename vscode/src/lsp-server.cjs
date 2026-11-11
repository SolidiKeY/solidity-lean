#!/usr/bin/env node
'use strict';
const {mkdtempSync,mkdirSync,rmSync}=require('node:fs');
const {join,resolve,dirname}=require('node:path');
const {fileURLToPath,pathToFileURL}=require('node:url');
const {createHash}=require('node:crypto');
const {fork}=require('node:child_process');
const {RpcPeer,failure,cancellable}=require('./rpc.cjs');
const {WorkerPool,fingerprint}=require('./worker-pool.cjs');
const {trackChild,waitForClose,waitForGroup}=require('./child-lifetime.cjs');
const {terminateTree,parseReport}=require('./backend.cjs');
const model=require('./model.cjs');
const {migrateDiagnostics}=require('./diagnostic-state.cjs');
const lookup=require('./lookup-state.cjs');
const language=require('./language-services.cjs');
const projects=require('./project.cjs');
const sourceText=require('./solidity-text.cjs');
const {versionNotification}=require('./startup.cjs');
const fs=require('node:fs');
const hash=text=>createHash('sha256').update(text).digest('hex');
const defaultSettings={workers:1,timeoutMs:60000,automaticVerification:'never',counterexamples:false,auditPreconditions:false};
const checkVersion=(doc,version)=>{if(!doc||version!==undefined&&doc.version!==version)throw failure('Document content changed',-32801);};
function settings(value={}){
  const result={...defaultSettings,...value};
  if(!Number.isSafeInteger(result.workers)||result.workers<1||result.workers>4)throw failure('workers must be between 1 and 4',-32602);
  if(!Number.isSafeInteger(result.timeoutMs)||result.timeoutMs<1||result.timeoutMs>3600000)throw failure('Invalid verification timeout',-32602);
  for(const key of ['includePaths','remappings'])if(result[key]!==undefined&&(!Array.isArray(result[key])||result[key].some(x=>typeof x!=='string')))throw failure('Invalid '+key,-32602);
  if(!['never','change','save'].includes(result.automaticVerification))throw failure('Invalid automaticVerification',-32602);
  return result;
}

const VERIFIER_GENERATION=Symbol('verifier generation');

class SolidityService {
  constructor(peer,root,configuration={},testing={}){
    this.peer=peer;this.root=resolve(root);this.settings=settings(configuration);this.docs=new Map();this.cache=new Map();this.requests=new Map();this.hits=0;this.misses=0;
    this.fingerprint=testing.fingerprint||(()=>fingerprint(this.root));this.generation=this.fingerprint();this.testing=testing;
    mkdirSync(join(this.root,'.lake'),{recursive:true});this.directory=mkdtempSync(join(this.root,'.lake/editor-lsp-'));
    this.analysisPool=new WorkerPool(this.root,join(this.directory,'analysis'),1,this.workerOptions('analysis'));
    this.pool=new WorkerPool(this.root,join(this.directory,'proof'),this.settings.workers,this.workerOptions('proof'));
    this.closed=false;
  }
  registerOwned(kind,child){const params={pid:child.pid,birth:child.processBirth,kind};if(this.peer.ownedProcessRegistration&&this.peer.request)return this.peer.request('solidityLean/registerOwnedProcess',params,{timeoutMs:this.settings.timeoutMs}).then(accepted=>{if(accepted!==true)throw failure('Owner refused child registration',-32800);});this.notify('solidityLean/ownedProcess',{event:'spawn',...params});}
  releaseOwned(kind,child){this.notify('solidityLean/ownedProcess',{event:'closed',kind,pid:child.pid,birth:child.processBirth});}
  workerOptions(kind,extra={}){return{...extra,onSpawn:child=>this.registerOwned(kind,child),onRetire:child=>this.releaseOwned(kind,child)};}
  notify(method,params){if(!this.closed&&!this.peer.closed)this.peer.notify(method,params);}
  current(doc,version,generation=this.generation){return !this.closed&&this.docs.get(doc.uri)===doc&&doc.version===version&&this.generation===generation;}
  status(doc,state,extra={}){
    const functions=doc.index?.nodes.filter(n=>n.nodeType==='FunctionDefinition').map(node=>{let parent=doc.index.parents.get(node);while(parent&&parent.nodeType!=='ContractDefinition')parent=doc.index.parents.get(parent);return{range:doc.index.nameRange(node),name:(parent?.name?parent.name+'.':'')+(node.name||node.kind||'constructor'),status:'ready'};}).filter(row=>row.range);
    this.notify('solidityLean/status',{uri:doc.uri,version:doc.version,sourceHash:hash(doc.text),synchronizationId:doc.synchronizationId,state,progressScope:'document',functions:state==='cancelled'?[]:functions,...extra});
  }
  diagnostics(doc,diagnostics){this.notify('textDocument/publishDiagnostics',{uri:doc.uri,version:doc.version,sourceHash:hash(doc.text),synchronizationId:doc.synchronizationId,diagnostics});}
  cancel(doc){
    if(!doc)return;clearTimeout(doc.timer);doc.analysisAbort?.abort();doc.verifyAbort?.abort();
    // A new verification must never join the compiler promise just cancelled
    // by its preceding cancel request (for example while symbols are loading).
    doc.analysisPromise=null;this.status(doc,'cancelled');
  }
  open(document){
    if(!Number.isSafeInteger(document.version)||typeof document.text!=='string'||Buffer.byteLength(document.text)>8*1024*1024)throw failure('Invalid or oversized document',-32602);
    const path=fileURLToPath(document.uri);if(!path.endsWith('.sol'))throw failure('Only Solidity files are supported',-32602);
    if(document.synchronizationId!==undefined&&(typeof document.synchronizationId!=='string'||!document.synchronizationId.length||document.synchronizationId.length>128))throw failure('Invalid synchronization identity',-32602);
    this.cancel(this.docs.get(document.uri));
    const doc={uri:document.uri,path,text:document.text,version:document.version,synchronizationId:document.synchronizationId};this.docs.set(doc.uri,doc);this.invalidatePath(doc.path,doc);this.schedule(doc);return doc;
  }
  change(params){
    const doc=this.docs.get(params.textDocument.uri);if(!doc)throw failure('Document is not open',-32602);
    if(!Number.isSafeInteger(params.textDocument.version)||params.textDocument.version<=doc.version)throw failure('Document version must increase',-32602);
    const text=language.applyChanges(doc.text,params.contentChanges);
    if(Buffer.byteLength(text)>8*1024*1024)throw failure('Document exceeds 8 MiB',-32602);
    const migrated=migrateDiagnostics(doc.verificationDiagnostics||[],doc.uri,doc.uri,doc.text,params.contentChanges);
    const migratedLookup=lookup.migrate(doc.lookup,doc.text,params.contentChanges,params.textDocument.version);
    this.cancel(doc);Object.assign(doc,{lookup:migratedLookup,verificationDiagnostics:migrated,text,version:params.textDocument.version,compiled:null,index:null,analysisPromise:null,verifyPromise:null,report:null});
    this.diagnostics(doc,migrated);this.invalidatePath(doc.path,doc);this.schedule(doc);
  }
  invalidatePath(path,except){
    for(const doc of this.docs.values())if(doc!==except&&(doc.compiled?.project||doc.projectSnapshot)&&Object.values((doc.compiled?.project||doc.projectSnapshot).files).some(f=>projects.identity(f.path)===projects.identity(path))){
      if(projects.current(doc.compiled?.project||doc.projectSnapshot,this.projectDocuments()))continue;
      this.cancel(doc);Object.assign(doc,{compiled:null,index:null,lookup:null,report:null,verificationDiagnostics:[]});this.diagnostics(doc,[]);this.notify('solidityLean/invalidated',{uri:doc.uri,version:doc.version,synchronizationId:doc.synchronizationId});this.schedule(doc);
    }
  }
  projectDocuments(){return [...this.docs.values()].map(d=>({path:d.path,text:d.text,version:d.version}));}
  async workspaceIndices(signal,filter={}){
    if(this.closed)throw failure('Service closed',-32800);
    const root=resolve(this.settings.projectRoot||dirname(this.docs.values().next().value?.path||join(this.root,'main.sol'))),paths=new Set();
    const walk=directory=>{if(signal?.aborted)throw failure('Request cancelled',-32800);for(const entry of fs.readdirSync(directory,{withFileTypes:true})){
      if(['.git','.lake','.cache','node_modules','out','build'].includes(entry.name))continue;
      const path=join(directory,entry.name);if(entry.isDirectory())walk(path);else if(entry.isFile()&&path.endsWith('.sol')){paths.add(path);if(paths.size>10000)throw failure('Workspace search exceeds 10000 source files',-32602);}
    }};walk(root);
    for(const doc of this.docs.values())if(!require('node:path').relative(root,doc.path).startsWith('..'))paths.add(doc.path);
    const generation=this.generation,epoch=this.buildEpoch,documents=[...this.docs.values()].map(doc=>({doc,version:doc.version,text:doc.text}));
    const validate=()=>{if(signal?.aborted)throw failure('Request cancelled',-32800);if(this.closed||generation!==this.generation||epoch!==this.buildEpoch||documents.length!==this.docs.size||documents.some(({doc,version,text})=>this.docs.get(doc.uri)!==doc||doc.version!==version||doc.text!==text))throw failure('Workspace changed',-32801);};
    const result=[];result.failures=[];let analyzed=0;
    for(const path of paths){
      if(signal?.aborted)throw failure('Request cancelled',-32800);
      const doc=this.docs.get(pathToFileURL(path).href);let capturedProject;
      try{
        const candidateText=doc?.text??fs.readFileSync(path,'utf8');
        if(filter.query&&!candidateText.toLowerCase().includes(filter.query.toLowerCase()))continue;
        capturedProject=projects.snapshot(path,candidateText,this.settings,this.projectDocuments());
        if(filter.target&&!Object.values(capturedProject.files).some(f=>projects.identity(f.path)===projects.identity(fileURLToPath(filter.target))))continue;
        if(++analyzed>256)throw failure('Workspace search exceeds 256 matching compilation roots',-32602);
        if(doc){await cancellable(this.analyze(doc),signal);validate();if(doc.index)result.push({index:doc.index,project:doc.compiled.project});}
        else {
          const text=fs.readFileSync(path,'utf8'),project=projects.snapshot(path,text,this.settings,this.projectDocuments());
          const compiled=await this.analysisPool.run({action:'analyze',source:path,text,project},{signal,timeoutMs:this.settings.timeoutMs});
          if(!projects.current(project,this.projectDocuments()))throw failure('Workspace changed',-32801);
          result.push({index:language.index(text,compiled.rawAst,{asts:compiled.rawAsts,files:project.files,uri:pathToFileURL(path).href}),project});
        }
      }catch(error){if([-32800,-32801,-32602].includes(error.code))throw error;result.failures.push({path,project:capturedProject});this.notify('window/logMessage',{type:3,message:`Workspace index: ${path}: ${error.message}`});}
    }
    result.validate=()=>{validate();if(result.some(item=>item.project&&!projects.current(item.project,this.projectDocuments())))throw failure('Workspace changed',-32801);};
    result.validate();return result;
  }
  async workspaceSymbols(query,signal){
    const indices=await this.workspaceIndices(signal,{query});indices.validate?.();
    const items=[];for(const {index}of indices)for(const declaration of index.declarations.values()){
      if(!declaration.name?.toLowerCase().includes((query||'').toLowerCase()))continue;
      const location=index.location(declaration);if(location.range)items.push({name:declaration.name,kind:declaration.nodeType==='FunctionDefinition'?12:5,location:{uri:location.uri,range:location.range}});
    }
    return [...new Map(items.map(i=>[JSON.stringify(i.location),i])).values()];
  }
  async referenceLocations(doc,target,include,signal,strict=false){
    const identity=doc.index.location(target);identity.uri??=doc.uri;
    const key=x=>JSON.stringify([x.uri,x.range]);
    const found=doc.index.locations(target,include).map(l=>({...l,uri:l.uri||doc.uri}));
    const indices=this.settings.projectRoot?await this.workspaceIndices(signal,{target:identity.uri}):[];
    indices.validate?.();
    if(strict&&indices.failures?.some(f=>!f.project||Object.values(f.project.files).some(file=>projects.identity(file.path)===projects.identity(fileURLToPath(identity.uri)))))throw failure('Fix dependent compiler errors before renaming',-32602);
    for(const {index}of indices){
      const declaration=[...index.declarations.values()].find(n=>key(index.location(n))===key(identity));
      if(declaration)found.push(...index.locations(declaration,include));
    }
    if(indices.some(({project})=>project&&!projects.current(project,this.projectDocuments())))throw failure('Workspace changed',-32801);
    return [...new Map(found.map(l=>[key(l),l])).values()];
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
  close(uri){const doc=this.docs.get(uri);this.cancel(doc);if(doc)this.diagnostics(doc,[]);this.docs.delete(uri);if(doc)this.invalidatePath(doc.path);}
  reset(configuration=this.settings){
    if(this.closed)throw failure('Service closed',-32800);
    const checked=settings(configuration);this.buildEpoch=(this.buildEpoch||0)+1;const build=this.buildChild;this.buildChild=null;
    for(const doc of this.docs.values())this.cancel(doc);
    this.retirement=Promise.all([this.retirement,this.analysisPool.dispose(),this.pool.dispose(),...(build?[waitForClose(build,{kill:true})]:[])]).then(()=>undefined);this.retirement.catch(()=>{});this.cache.clear();this.settings=checked;
    this.analysisPool=new WorkerPool(this.root,join(this.directory,'analysis-'+this.buildEpoch),1,this.workerOptions('analysis',{startAfter:this.retirement}));
    this.pool=new WorkerPool(this.root,join(this.directory,'proof-'+this.buildEpoch),this.settings.workers,this.workerOptions('proof',{startAfter:this.retirement}));
    this.buildPromise=null;this.buildInputSnapshot=null;this.legacyBuilt=false;
    for(const doc of this.docs.values()){Object.assign(doc,{compiled:null,index:null,analysisPromise:null,verifyPromise:null,report:null,lookup:null,verificationDiagnostics:[]});this.diagnostics(doc,[]);}
    return this.retirement;
  }
  buildInputs(){return this.testing.fingerprint?this.fingerprint():fingerprint(this.root,{buildInputs:true});}
  refresh(){if(this.buildInputSnapshot&&this.buildInputs()===this.buildInputSnapshot)return;const next=this.fingerprint();if(next!==this.generation){this.reset();this.generation=next;}}
  async build(){
    if(this.closed)throw failure('Service closed',-32800);
    if(this.testing.verify)return;
    if(this.buildPromise)return this.buildPromise;
    const epoch=this.buildEpoch||0;
    const operation=(async()=>{
      await this.retirement;if(this.closed||epoch!==(this.buildEpoch||0))throw failure('Backend build cancelled',-32800);
      const sourceBefore=this.buildInputs();this.buildInputSnapshot=sourceBefore;
      const {lakeCommand}=await import(pathToFileURL(join(this.root,'scripts/lake-command.mjs')).href);
      if(this.closed||epoch!==(this.buildEpoch||0))throw failure('Backend build cancelled',-32800);
      await new Promise((resolvePromise,reject)=>{
        const command=lakeCommand(),child=fork(join(__dirname,'build-launcher.cjs'),[],{cwd:this.root,detached:process.platform!=='win32',stdio:['ignore','pipe','pipe','ipc']});
        child.ownedGroup=process.platform!=='win32';trackChild(child);this.buildChild=child;let log='',admitted=false;const collect=chunk=>{log=(log+chunk).slice(-16000);};child.stdout.on('data',collect);child.stderr.on('data',collect);
        const deadline=Date.now()+this.settings.timeoutMs;
        const rejectOwned=error=>{try{terminateTree(child);}catch{}clearTimeout(timer);reject(error);};
        const timer=setTimeout(()=>rejectOwned(failure('Backend build timed out',-32800)),this.settings.timeoutMs);
        Promise.resolve(this.registerOwned('build',child)).then(()=>{if(this.closed||epoch!==(this.buildEpoch||0))throw failure('Backend build cancelled',-32800);admitted=true;child.send({command,args:['build','Solidity.Frontend.Testing']},error=>{if(error)rejectOwned(error);});}).catch(rejectOwned);
        child.once('error',rejectOwned);
        child.once('close',code=>{waitForGroup(child,{deadline}).then(()=>{this.releaseOwned('build',child);clearTimeout(timer);if(this.buildChild===child)this.buildChild=null;if(code===0&&admitted)resolvePromise();else reject(new Error('Backend build failed: '+log));},rejectOwned).catch(rejectOwned);});
      });
      if(this.closed||epoch!==(this.buildEpoch||0))throw failure('Backend build cancelled',-32800);
      if(this.buildInputs()!==sourceBefore)throw failure('Backend sources changed during build',-32801);
      // A successful build updates artifact identities. Nothing is cached yet.
      this.generation=this.fingerprint();this.cache.clear();this.legacyBuilt=true;this.buildInputSnapshot=null;
    })();
    const pending=operation.catch(error=>{if(this.buildPromise===pending){this.buildPromise=null;this.buildInputSnapshot=null;this.legacyBuilt=false;}throw error;});
    this.buildPromise=pending;return pending;
  }
  async analyze(doc,{refresh=true}={}){
    if(this.closed)throw failure('Service closed',-32800);
    if(refresh)this.refresh();
    if(doc.compiled){
      const contentCurrent=!doc.compiled.project||projects.current(doc.compiled.project,this.projectDocuments());
      if(contentCurrent&&(!doc.compiled.project||projects.current(doc.compiled.project,this.projectDocuments(),true)))return doc.compiled;
      Object.assign(doc,{compiled:null,index:null});
      if(!contentCurrent){doc.lookup=null;doc.report=null;doc.verificationDiagnostics=[];this.diagnostics(doc,[]);this.notify('solidityLean/invalidated',{uri:doc.uri,version:doc.version,synchronizationId:doc.synchronizationId});}
    }
    if(doc.analysisPromise)return doc.analysisPromise;
    const version=doc.version,generation=this.generation,text=doc.text,controller=new AbortController();doc.analysisAbort=controller;
    doc.analysisPromise=(async()=>{
      this.status(doc,'compiling');const start=Date.now();
      try{
        const project=this.testing.analyze?null:projects.snapshot(doc.path,text,this.settings,[...this.docs.values()]);doc.projectSnapshot=project;
        const compiled=this.testing.analyze?await this.testing.analyze(doc,controller.signal):await this.analysisPool.run({action:'analyze',source:doc.path,text,project},{signal:controller.signal,timeoutMs:this.settings.timeoutMs});
        if(!this.current(doc,version,generation)||controller.signal.aborted)throw failure('Document content changed',-32801);
        if((compiled.sourceHash??compiled.fixture?.header.sourceSha256)!==hash(text))throw new Error('Compiler source hash mismatch');
        if(compiled.project&&!projects.current(compiled.project,[...this.docs.values()]))throw failure('Imported source changed',-32801);
        doc.compiled=compiled;doc.compileMs=Date.now()-start;doc.index=language.index(text,compiled.rawAst,{asts:compiled.rawAsts,files:compiled.project?.files,uri:doc.uri});
        doc.lookup=lookup.snapshot(doc.index,doc,this.generation);
        const proofDiagnostics=doc.verificationDiagnostics||[];
        this.diagnostics(doc,[...this.compilerDiagnostics(doc,compiled.diagnostics),...proofDiagnostics]);if(!doc.verifyPromise&&!doc.report)this.status(doc,'ready');return compiled;
      }catch(error){
        if(this.current(doc,version,generation)&&!controller.signal.aborted&&doc.analysisAbort===controller&&![-32800,-32801].includes(error.code)){this.diagnostics(doc,[...this.compilerDiagnostics(doc,error.diagnostics||[{severity:'error',message:error.message}]),...(doc.verificationDiagnostics||[])]);this.status(doc,'error',{phase:'compilation',message:error.message});}
        throw error;
      }
    })();
    const pending=doc.analysisPromise;
    try{return await pending;}finally{if(doc.analysisPromise===pending)doc.analysisPromise=null;}
  }
  compilerDiagnostics(doc,diagnostics=[]){
    const project=doc.compiled?.project??doc.projectSnapshot;
    const locate=location=>{
      const file=project?.files[location?.file];
      const text=file?.text??(!location?.file||location.file===doc.path?doc.text:null);
      const range=text!==null&&location&&Number.isInteger(location.start)&&Number.isInteger(location.end)&&location.start>=0&&location.end>=location.start?
        language.byteRange(text,`${location.start}:${location.end-location.start}:0`):null;
      return {file,range};
    };
    return diagnostics.filter(d=>['error','warning'].includes(d.severity)).map(d=>{
      const primary=locate(d.sourceLocation),foreign=primary.file?projects.identity(primary.file.path)!==projects.identity(doc.path):!!d.sourceLocation?.file&&d.sourceLocation.file!==doc.path;
      const related=[];
      if(foreign&&primary.file)related.push({location:{uri:pathToFileURL(primary.file.path).href,range:primary.range||model.rangeOf({})},message:d.message});
      for(const secondary of d.secondarySourceLocations||[]){
        const {file,range}=locate(secondary);if(!file||!range)continue;
        related.push({location:{uri:pathToFileURL(file.path).href,range},message:secondary.message||d.message});
      }
      const unique=[...new Map(related.map(r=>[JSON.stringify(r),r])).values()];
      return {range:foreign?model.rangeOf({}):primary.range||model.rangeOf({}),severity:d.severity==='error'?1:2,source:'solc',code:foreign?'import:'+d.errorCode:d.errorCode,message:d.formattedMessage||d.message,
        ...(unique.length?{relatedInformation:unique}:{})};
    });
  }

  reportDiagnostics(report){
    const serialize=d=>({range:d.range,severity:d.severity==='error'?1:2,message:d.message,code:d.code,source:'Solidity Lean'});
    return [...report.results.flatMap(row=>model.diagnostics({results:[row],errors:[]}).map(d=>({...serialize(d),data:{solidityLean:{contract:row.contract,function:row.signature||row.function}}}))),
      ...model.diagnostics({results:[],errors:report.errors}).map(serialize)];
  }
  publish(doc,report,cacheHit=false,selection={}){
    const full=selection.function&&doc.report?{...report,results:[...doc.report.results.filter(old=>!report.results.some(r=>r.contract===old.contract&&(r.signature||r.function)===(old.signature||old.function))),...report.results]}:report;
    doc.report=full;
    const converted=this.reportDiagnostics(full);
    const retained=selection.function?(doc.verificationDiagnostics||[]).filter(d=>{
      if(!d.message.startsWith('Outdated: '))return false;
      const owner=d.data?.solidityLean;
      return !owner||!((!selection.contract||owner.contract===selection.contract)&&owner.function===selection.function)
        &&!full.results.some(row=>row.contract===owner.contract&&(row.signature||row.function)===owner.function);
    }):[];
    doc.verificationDiagnostics=[...retained,...converted];
    this.diagnostics(doc,[...this.compilerDiagnostics(doc,doc.compiled?.diagnostics),...doc.verificationDiagnostics]);
    this.notify('solidityLean/report',{uri:doc.uri,version:doc.version,synchronizationId:doc.synchronizationId,sourceHash:hash(doc.text),report,cacheHit,selection:{function:selection.function,contract:selection.contract}});
    this.status(doc,'complete',{cacheHit,progressScope:'functions',errors:full.errors.length,functions:full.results.map(r=>({range:model.rangeOf(r),name:model.label(r),status:r.status,verification:r.verification,preconditions:r.preconditions}))});
  }
  async verify(uri,options={},signal){
    const doc=this.docs.get(uri);checkVersion(doc,options.version);clearTimeout(doc.timer);
    if(options.timeoutMs!==undefined&&(!Number.isSafeInteger(options.timeoutMs)||options.timeoutMs<1||options.timeoutMs>3600000))throw failure('Invalid verification timeout',-32602);
    this.refresh();
    const requestedVersion=doc.version,requestedText=doc.text,requestedGeneration=this.generation,requestedEpoch=this.buildEpoch;
    if(signal?.aborted)throw failure('Request cancelled',-32800);
    const prepared=await cancellable(this.analyze(doc,{refresh:false}),signal);
    if(signal?.aborted)throw failure('Request cancelled',-32800);
    if(!this.current(doc,requestedVersion,requestedGeneration)||doc.text!==requestedText||this.buildEpoch!==requestedEpoch||(prepared.sourceHash??prepared.fixture?.header.sourceSha256)!==hash(requestedText)||prepared.project&&!projects.current(prepared.project,this.projectDocuments()))throw failure('Document or backend changed',-32801);
    const projectDigest=prepared.project?.digest??'';
    const key=JSON.stringify([uri,hash(doc.text),this.generation,projectDigest,!!options.listing,options.contract||'',options.function||'',
      options.counterexamples??this.settings.counterexamples,options.auditPreconditions??this.settings.auditPreconditions,options.certify===true]);
    if(doc.verifyPromise&&doc.verifyKey===key&&!doc.verifyAbort?.signal.aborted)return this.joinVerification(doc.verifyJob,signal);
    doc.verifyAbort?.abort();const controller=new AbortController();doc.verifyAbort=controller;doc.verifyKey=key;
    const job={controller,callers:new Set(),finished:false};doc.verifyJob=job;
    const version=doc.version,text=doc.text;
    const pending=(async()=>{
      if(controller.signal.aborted)throw failure('Request cancelled',-32800);
      const cached=this.cache.get(key);
      if(cached){
        const generation=this.generation;
        await this.analyze(doc);
        if(!this.current(doc,version,generation)||doc.verifyAbort!==controller||this.fingerprint()!==generation||controller.signal.aborted||prepared.project&&!projects.current(prepared.project,[...this.docs.values()]))throw failure('Document or backend changed',-32801);
        this.cache.delete(key);this.cache.set(key,cached);this.hits++;this.publish(doc,cached,true,options);return cached;
      }
      this.misses++;this.status(doc,'queued');
      try{
        const compiled=prepared;if(controller.signal.aborted)throw failure('Request cancelled',-32800);
        if(!this.current(doc,version)||controller.signal.aborted)throw failure('Request cancelled',-32800);
        let generation=this.generation;this.status(doc,'running');const start=Date.now();
        const task={action:'verify',source:doc.path,text,compiled,options:{...this.settings,...options}};
        const report=this.testing.verify?await this.testing.verify(task,controller.signal):await this.prove(task,controller.signal);
        generation=report[VERIFIER_GENERATION]??generation;
        if(!this.current(doc,version,generation)||doc.verifyAbort!==controller||this.fingerprint()!==generation||controller.signal.aborted||compiled.project&&!projects.current(compiled.project,[...this.docs.values()]))throw failure('Document or backend changed',-32801);
        parseReport(JSON.stringify(report));
        if(report.results.some(row=>row.source!==doc.path||row.sourceHash!==hash(text)))throw new Error('Verification source identity mismatch');
        if((!task.options.counterexamples||options.listing)&&report.results.some(r=>r.status==='refuted'&&r.verification!=='direct'))throw new Error('Unrequested counterexample evidence');
        if(task.options.auditPreconditions&&!options.listing&&report.results.some(r=>r.preconditions===undefined))throw new Error('Missing requested precondition audit');
        report.timings={compileMs:doc.compileMs,proofMs:Date.now()-start};
        // Recompute the key after the initial build changed artifact identities.
        const storedKey=JSON.stringify([uri,hash(text),generation,compiled.project?.digest??'',!!options.listing,options.contract||'',options.function||'',task.options.counterexamples,task.options.auditPreconditions,task.options.certify===true]);
        this.cache.set(storedKey,report);while(this.cache.size>32)this.cache.delete(this.cache.keys().next().value);
        this.publish(doc,report,false,options);return report;
      }catch(error){
        if(this.current(doc,version)&&doc.verifyAbort===controller)this.status(doc,[-32800,-32801].includes(error.code)?'cancelled':'error',{message:error.message});
        throw error;
      }
    })();
    doc.verifyPromise=pending;
    job.promise=pending;const cleanup=()=>{job.finished=true;if(doc.verifyPromise===pending){doc.verifyPromise=null;doc.verifyJob=null;}};pending.then(cleanup,cleanup);
    return this.joinVerification(job,signal);
  }
  joinVerification(job,signal){
    const caller={};job.callers.add(caller);
    return new Promise((resolve,reject)=>{
      let settled=false;const finish=(error,value)=>{if(settled)return;settled=true;signal?.removeEventListener('abort',abort);job.callers.delete(caller);if(error?.code===-32800&&!job.finished&&!job.callers.size)job.controller.abort();error?reject(error):resolve(value);};
      const abort=()=>finish(failure('Request cancelled',-32800));
      signal?.addEventListener('abort',abort,{once:true});job.promise.then(value=>finish(null,value),error=>finish(error));if(signal?.aborted)abort();
    });
  }
  wait(promise,signal){
    if(!signal)return promise;if(signal.aborted)return Promise.reject(failure('Request cancelled',-32800));
    return new Promise((resolvePromise,reject)=>{
      const abort=()=>reject(failure('Request cancelled',-32800));signal.addEventListener('abort',abort,{once:true});
      promise.then(resolvePromise,reject).finally(()=>signal.removeEventListener('abort',abort));
    });
  }
  async prove(task,signal,deadline=Date.now()+task.options.timeoutMs){
    const controller=new AbortController();
    const timer=setTimeout(()=>controller.abort(),Math.max(1,deadline-Date.now()));
    const abort=()=>controller.abort();signal?.addEventListener('abort',abort,{once:true});if(signal?.aborted)abort();
    let usedGeneration=this.generation;
    const run=async work=>{
      let report=await this.pool.run({...work,deferLegacyBuild:!this.legacyBuilt},{signal:controller.signal,timeoutMs:Math.max(1,deadline-Date.now())});
      if(report.needsLegacyBuild){
        await this.wait(this.build(),controller.signal);usedGeneration=this.generation;
        if(controller.signal.aborted)throw failure('Request cancelled',-32800);
        report=await this.pool.run({...work,deferLegacyBuild:false},{signal:controller.signal,timeoutMs:Math.max(1,deadline-Date.now())});
      }
      Object.defineProperty(report,VERIFIER_GENERATION,{value:usedGeneration});return report;
    };
    try{
      if(this.settings.workers===1||task.options.function||task.options.listing)return await run(task);
      const listing=await run({...task,options:{...task.options,listing:true}}),ready=listing.results.filter(r=>r.status==='ready');
      if(listing.errors.length||ready.length<2||task.options.auditPreconditions&&listing.results.some(r=>r.status!=='ready'))return await run(task);
      const reports=await Promise.all(ready.map(row=>run({...task,options:{...task.options,contract:row.contract,function:row.signature||row.function}})));
      if(listing[VERIFIER_GENERATION]!==usedGeneration||reports.some(r=>r[VERIFIER_GENERATION]!==usedGeneration))return await this.prove(task,signal,deadline);
      const results=listing.results.map(row=>{
        if(row.status!=='ready')return row;
        const report=reports[ready.indexOf(row)],matches=report.results.filter(r=>r.contract===row.contract&&(r.signature||r.function)===(row.signature||row.function));
        if(matches.length!==1)throw new Error('Function worker returned a different verification selection');return matches[0];
      });
      return {[VERIFIER_GENERATION]:usedGeneration,results,errors:[...new Map(reports.flatMap(r=>r.errors).map(e=>[JSON.stringify(e),e])).values()],
        backend:{...reports[0].backend,verificationMode:'functions',workers:[...new Map(reports.map(r=>[r.backend.workerPid,r.backend])).values()]}};
    }catch(error){controller.abort();throw error;}finally{clearTimeout(timer);signal?.removeEventListener('abort',abort);}
  }
  async language(method,params,signal){
    const doc=this.docs.get(params.textDocument.uri);checkVersion(doc,params.textDocument.version);
    const version=doc.version;
    if(signal?.aborted)throw failure('Request cancelled',-32800);
    try{await cancellable(this.analyze(doc),signal);}catch(error){if([-32800,-32801].includes(error.code))throw error;}
    if(signal?.aborted)throw failure('Request cancelled',-32800);
    if(!this.current(doc,version))throw failure('Document content changed',-32801);
    if(!doc.index&&lookup.methods.has(method)&&doc.lookup){
      if(doc.lookup.version!==doc.version||doc.lookup.generation!==this.generation||!projects.current(doc.lookup.dependencies,this.projectDocuments()))doc.lookup=null;
      else return lookup.query(doc.lookup,method,params);
    }
    if(method==='textDocument/formatting'){
      const formatted=sourceText.format(doc.text,params.options);if(formatted===doc.text)return [];
      if(doc.compiled){
        const documents=this.projectDocuments().map(d=>d.path===doc.path?{...d,text:formatted}:d),project=projects.snapshot(doc.path,formatted,this.settings,documents);
        const checked=await this.analysisPool.run({action:'analyze',source:doc.path,text:formatted,project},{signal,timeoutMs:this.settings.timeoutMs});
        const annotations=ast=>{const values=[];const visit=n=>{if(!n||typeof n!=='object')return;if(n.nodeType&&(n.documentation?.text||n.loopSpec))values.push([n.nodeType,n.documentation?.text,n.loopSpec]);for(const v of Object.values(n))if(v&&typeof v==='object'){if(Array.isArray(v))v.forEach(visit);else visit(v);}};visit(ast);return JSON.stringify(values);};
        if(annotations(checked.annotationAst??checked.primaryAst)!==annotations(doc.compiled.annotationAst??doc.compiled.primaryAst))throw failure('Formatting would change specification attachment',-32602);
      }
      if(!this.current(doc,version))throw failure('Document content changed',-32801);
      return [{range:{start:{line:0,character:0},end:language.position(doc.text,doc.text.length)},newText:formatted}];
    }
    if(method==='textDocument/codeAction')return this.codeActions(doc,params);
    if(method==='textDocument/completion')return language.completion(doc.text,params.position,doc.index);
    if(method==='textDocument/documentSymbol')return doc.index?.symbols||[];
    if(method==='textDocument/signatureHelp')return language.signatureHelp(doc.text,params.position,doc.index);
    const occurrence=doc.index?.occurrence(params.position),target=occurrence?.declaration;
    if(method==='textDocument/hover'){
      const rows=doc.report?.results.filter(r=>language.contains(model.rangeOf(r),params.position));
      const row=rows?.find(r=>r.sourceId>=0)||rows?.[0];
      if(row)return {contents:{kind:'plaintext',value:model.detail(row)},range:model.rangeOf(row)};
      if(!target)return null;
      return {contents:{kind:'markdown',value:language.hoverContent(doc.index,target)},range:occurrence.range};
    }
    if(!target)return method==='textDocument/references'||method==='textDocument/documentHighlight'?[]:null;
    if(method==='textDocument/definition'){const l=doc.index.location(target);return {uri:l.uri||doc.uri,range:l.range};}
    const locations=await this.referenceLocations(doc,target,params.context?.includeDeclaration??true,signal,method==='textDocument/rename');
    if(!this.current(doc,version))throw failure('Document content changed',-32801);
    const ranges=locations.filter(l=>l.uri===doc.uri).map(l=>l.range);
    if(method==='textDocument/references')return locations.map(({uri,range})=>({uri,range}));
    if(method==='textDocument/documentHighlight')return ranges.map(range=>({range,kind:1}));
    if(method==='textDocument/prepareRename')return {range:occurrence.range,placeholder:target.name};
    if(method==='textDocument/rename'){
      if(!language.validIdentifier(params.newName))throw failure('Invalid Solidity identifier',-32602);
      if([...doc.index.declarations.values()].some(n=>n.id!==target.id&&n.name===params.newName))throw failure('Rename would collide with an existing declaration',-32602);
      const escaped=(target.name||'').replace(/[.*+?^${}()|[\]\\]/g,'\\$&');
      if(doc.index.nodes.some(n=>typeof n.documentation?.text==='string'&&new RegExp(`(?<![\\w$])${escaped}(?![\\w$])`).test(n.documentation.text)))throw failure('Rename involving specification text requires a manual specification update',-32602);
      const grouped=new Map();for(const location of locations){
        const uri=location.uri||doc.uri;if(!grouped.has(uri))grouped.set(uri,{textDocument:{uri,version:location.version??null},edits:[]});
        grouped.get(uri).edits.push({range:location.range,newText:params.newName});
      }
      const edits={documentChanges:[...grouped.values()]};await this.validateEdits(doc,edits,signal,new Map(locations.map(l=>[l.uri,l.sourceHash])));return edits;
    }
    return null;
  }
  codeActions(doc,params){
    const actions=[],add=(title,diagnostic,range,newText)=>actions.push({title,kind:'quickfix',diagnostics:[diagnostic],edit:{documentChanges:[{textDocument:{uri:doc.uri,version:doc.version},edits:[{range,newText}]}]}});
    if(params.context?.only&&!params.context.only.some(k=>'quickfix'.startsWith(k)))return [];
    for(const diagnostic of params.context?.diagnostics||[]){
      if(String(diagnostic.code)==='1878')for(const license of ['UNLICENSED','MIT','Apache-2.0'])add('Add SPDX license identifier: '+license,diagnostic,{start:{line:0,character:0},end:{line:0,character:0}},'// SPDX-License-Identifier: '+license+'\n');
      if(!['5667','2072'].includes(String(diagnostic.code))||!doc.index)continue;
      const variable=doc.index.nodes.find(n=>n.nodeType==='VariableDeclaration'&&n.name&&language.contains(doc.index.nodeRange(n),diagnostic.range.start));if(!variable)continue;
      const quoted=variable.name.replace(/[.*+?^${}()|[\]\\]/g,'\\$&');
      if(sourceText.tokens(doc.text).some(t=>t.kind==='comment'&&/@(?:custom:key|param|return)\b/.test(t.text)&&new RegExp('(?<![\\w$])'+quoted+'(?![\\w$])').test(t.text)))continue;
      const parent=doc.index.parents.get(variable);
      if(String(diagnostic.code)==='5667'&&parent?.nodeType==='ParameterList')add('Remove unused parameter name '+variable.name,diagnostic,doc.index.nameRange(variable),'');
      if(String(diagnostic.code)==='2072'&&parent?.nodeType==='VariableDeclarationStatement'&&parent.declarations.length===1&&(!parent.initialValue||parent.initialValue.nodeType==='Literal')&&/^(?:u?int\d*|bool|address|bytes\d+)$/.test(variable.typeName?.name||''))add('Remove unused local '+variable.name,diagnostic,doc.index.nodeRange(parent),'');
    }
    return actions;
  }

  async validateEdits(doc,edit,signal,expected=new Map()){
    const documents=this.projectDocuments(),baselines=[],originals=new Map();
    for(const change of edit.documentChanges){
      const path=fileURLToPath(change.textDocument.uri),open=this.docs.get(change.textDocument.uri),text=open?.text??fs.readFileSync(path,'utf8');
      if(change.textDocument.version!==null&&open?.version!==change.textDocument.version||expected.get(change.textDocument.uri)&&projects.hash(text)!==expected.get(change.textDocument.uri))throw failure('Refactoring target changed',-32801);
      originals.set(path,text);baselines.push(projects.snapshot(path,text,this.settings,this.projectDocuments()));
    }
    for(const change of edit.documentChanges){
      const path=fileURLToPath(change.textDocument.uri),text=originals.get(path);
      const sorted=[...change.edits].sort((a,b)=>language.offset(text,b.range.start)-language.offset(text,a.range.start));
      const changed=language.applyChanges(text,sorted.map(e=>({range:e.range,text:e.newText}))),existing=documents.find(d=>d.path===path);
      if(existing)existing.text=changed;else documents.push({path,text:changed});
    }
    for(const change of edit.documentChanges){
      const source=fileURLToPath(change.textDocument.uri),text=documents.find(d=>d.path===source).text,project=projects.snapshot(source,text,this.settings,documents);
      await this.analysisPool.run({action:'analyze',source,text,project},{signal,timeoutMs:this.settings.timeoutMs});
    }
    for(const change of edit.documentChanges)if(change.textDocument.version!==null&&this.docs.get(change.textDocument.uri)?.version!==change.textDocument.version)throw failure('Refactoring target changed',-32801);
    if(baselines.some(p=>!projects.current(p,this.projectDocuments())))throw failure('Workspace changed during refactoring',-32801);
  }

  dispose(){
    if(this.disposal)return this.disposal;
    for(const doc of this.docs.values())this.cancel(doc);
    for(const controller of this.requests.values())controller.abort();
    this.closed=true;this.buildEpoch=(this.buildEpoch||0)+1;const build=this.buildChild;this.buildChild=null;
    const parts={retirement:this.retirement,proofPool:this.pool.dispose(),analysisPool:this.analysisPool.dispose(),...(build?{build:waitForClose(build,{kill:true})}:{})};
    // Diagnostics only: a dispose still running after 1.5 s names its pending parts on stderr.
    const pending=new Set(Object.keys(parts)),started=Date.now();for(const [name,part] of Object.entries(parts))Promise.resolve(part).then(()=>pending.delete(name),error=>{pending.delete(name);process.stderr.write(`Server dispose part ${name} failed after ${Date.now()-started} ms: ${error?.message}\n`);});
    const watchdog=setTimeout(()=>{if(pending.size)process.stderr.write(`Server dispose still pending after ${Date.now()-started} ms: ${[...pending].join(', ')}\n`);},1500);watchdog.unref?.();
    this.disposal=Promise.all(Object.values(parts)).then(()=>{rmSync(this.directory,{recursive:true,force:true});}).finally(()=>clearTimeout(watchdog));this.disposal.catch(()=>{});return this.disposal;
  }
}

function startServer(input=process.stdin,output=process.stdout){
  const peer=new RpcPeer(input,output);let service,shuttingDown=false,versionSent=false;
  const identity=()=>({name:'Solidity Lean Language Server',version:require('../package.json').version});
  peer.on('handlerError',error=>{if(!peer.closed)peer.notify('window/logMessage',{type:1,message:error.message});});
  peer.onRequest('initialize',params=>{
    if(service)throw failure('Already initialized',-32600);
    peer.ownedProcessRegistration=params.capabilities?.experimental?.solidityLeanOwnedProcess===true;
    service=new SolidityService(peer,params.initializationOptions?.backendPath||fileURLToPath(params.rootUri),params.initializationOptions?.settings);
    return {serverInfo:identity(),capabilities:{textDocumentSync:{openClose:true,change:2,save:{includeText:true}},hoverProvider:true,
      completionProvider:{triggerCharacters:['.']},definitionProvider:true,referencesProvider:true,documentSymbolProvider:true,documentHighlightProvider:true,
      workspaceSymbolProvider:true,documentFormattingProvider:true,codeActionProvider:{codeActionKinds:['quickfix']},renameProvider:{prepareProvider:true},signatureHelpProvider:{triggerCharacters:['(',',']}}};
  });
  const ready=()=>{if(!service||shuttingDown)throw failure('Server is not initialized',-32002);return service;};
  peer.onNotification('initialized',()=>{if(!versionSent){ready();peer.notify(versionNotification,identity());versionSent=true;}});
  peer.onNotification('textDocument/didOpen',params=>ready().open(params.textDocument));
  peer.onNotification('textDocument/didChange',params=>ready().change(params));
  peer.onNotification('textDocument/didSave',params=>ready().save(params));
  peer.onNotification('textDocument/didClose',params=>ready().close(params.textDocument.uri));
  peer.onNotification('workspace/didChangeConfiguration',params=>{const s=ready();return s.reset(params.settings);});
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
    workers:service.pool.workers.map(w=>w.child.pid),analysisWorkers:service.analysisPool.workers.map(w=>w.child.pid),retiringWorkers:[...service.pool.workers,...service.analysisPool.workers].filter(w=>w.retiring).map(w=>w.child.pid),directory:service.directory,queued:service.pool.queue.length,generation:service.generation}));
  for(const method of ['hover','completion','definition','references','documentSymbol','signatureHelp','documentHighlight','prepareRename','rename','formatting','codeAction'])
    peer.onRequest('textDocument/'+method,async(params,id)=>{const s=ready(),controller=new AbortController();s.requests.set(id,controller);try{return await s.language('textDocument/'+method,params,controller.signal);}finally{s.requests.delete(id);}});
  peer.onRequest('workspace/symbol',async(params,id)=>{const s=ready(),controller=new AbortController();s.requests.set(id,controller);try{return await s.workspaceSymbols(params.query,controller.signal);}finally{s.requests.delete(id);}});
  peer.onNotification('workspace/didChangeWatchedFiles',params=>{for(const change of params.changes)ready().invalidatePath(fileURLToPath(change.uri));});
  peer.onRequest('shutdown',async()=>{shuttingDown=true;await service?.dispose();return null;});
  const exit=code=>Promise.resolve(service?.dispose()).then(()=>{if(input===process.stdin)process.exit(code);},error=>{process.stderr.write('Server cleanup failed: '+error.message+'\n');if(input===process.stdin)process.exit(1);});
  peer.onNotification('exit',()=>exit(shuttingDown?0:1));
  peer.on('close',()=>exit(shuttingDown?0:1));
  for(const signal of ['SIGINT','SIGTERM'])process.once(signal,()=>exit(0));
  return {peer,get service(){return service;}};
}
module.exports={SolidityService,startServer,settings};
if(require.main===module)startServer();
