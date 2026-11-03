import {compileFixture} from '../../scripts/solc-ast.mjs';
import language from '../../vscode/src/language-services.cjs';
import textTools from '../../vscode/src/solidity-text.cjs';
import projects from '../../vscode/src/project.cjs';
import model from '../../vscode/src/model.cjs';
import {files,writeFileSync,readFileSync,createHash} from './platform.mjs';
import {prepareProofs,verifyInBrowser,cancelProofs,abandonProofs} from './proofs.mjs';

const docs=new Map();let generation=0,compilations=0,compiledCache=new Map(),proofCache=new Map(),proofReady=false,proofChain=Promise.resolve(),activeProof,proofBoot=0,compilerReady,settings={automaticVerification:'never',workers:1};
const uri=name=>'file:///workspace/'+name;
const validName=name=>typeof name==='string'&&/^[A-Za-z0-9_$][A-Za-z0-9_.$-]*\.sol$/.test(name)&&name.length<=120;
const send=(method,params)=>postMessage({method,params});
function emit(method,doc,extra={}){send(method,{name:doc.name,uri:uri(doc.name),version:doc.version,...extra});}
const hash=text=>createHash('sha256').update(text).digest('hex');
const document=(name,version)=>{const doc=docs.get(name);if(!doc)throw new Error('Unknown Solidity document');if(version!==undefined&&version!==doc.version)throw Object.assign(new Error('Document content changed'),{code:-32801});return doc;};
const snapshots=()=>[...docs.values()].map(d=>({path:'/workspace/'+d.name,uri:uri(d.name),text:d.text,version:d.version}));
function invalidate(){if(activeProof){abandonProofs();activeProof=undefined;proofChain=Promise.resolve();}generation++;compiledCache.clear();proofCache.clear();for(const doc of docs.values()){doc.report=null;emit('invalidated',doc);}}

async function loadCompiler(){
  const response=await fetch('/compiler/soljson-v0.8.34+commit.80d5c536.js');if(!response.ok)throw new Error('The bundled Solidity compiler is missing');
  const bytes=new Uint8Array(await response.arrayBuffer());
  const pin='c8649f8d57f81b3244c7d2dd662efc0620d1ae296f623b347a2c616a6cfd11d8';
  if(createHash('sha256').update(bytes).digest('hex')!==pin)throw new Error('Bundled compiler checksum mismatch');
  const base='/runtime/solkey/keyext.solidity.core/';
  writeFileSync(base+'build/soljson/soljson-v0.8.34+commit.80d5c536.js',bytes);
  writeFileSync(base+'build.gradle',`ext.soljsonFile = "soljson-v0.8.34+commit.80d5c536.js"\next.soljsonSha256 = "${pin}"\n`);
  writeFileSync('/runtime/solkey/snapshot.json',JSON.stringify({commit:'browser-local-compiler'}));
  await new Promise((resolve,reject)=>{globalThis.Module={onRuntimeInitialized:resolve,onAbort:message=>reject(new Error(String(message)))};try{importScripts('/compiler/soljson-v0.8.34+commit.80d5c536.js');}catch(error){reject(error);}});
  send('runtime',{mode:'browser',compilerReady:true,proofReady:false,error:null,message:'Solidity compilation runs in this browser. Preparing the pinned Lean kernel.'});
  initializeProofs();
}
function resetProofs(replayAutomatic=false){cancelProofs();proofReady=false;activeProof=undefined;proofChain=Promise.resolve();proofBoot++;send('runtime',{mode:'browser',compilerReady:true,proofReady:false,error:null,message:'Preparing the browser proof worker.'});initializeProofs(replayAutomatic);}
async function initializeProofs(replayAutomatic=true){
  const boot=++proofBoot;
  try{
    const runtime=await prepareProofs(event=>{if(event.method==='log')send('log',{message:event.message});if(event.method==='restartRequired')resetProofs(true);});
    if(boot!==proofBoot)return;proofReady=true;send('runtime',{mode:'browser',compilerReady:true,proofReady:true,error:null,lean:runtime.version,verifier:runtime.kind||'lean-frontend',wasmBytes:runtime.wasmBytes,build:runtime.build,message:'The verifier and Solidity compiler run entirely in this browser.'});if(replayAutomatic&&settings.automaticVerification==='change')for(const doc of docs.values())schedule(doc);
  }catch(error){if(boot!==proofBoot)return;cancelProofs();proofReady=false;send('runtime',{mode:'browser',compilerReady:true,proofReady:false,error:error.message,message:'Unable to start Lean: '+error.message});}
}
async function verify(doc,options){
  const epoch=generation,version=doc.version,text=doc.text;
  const compiled=await analyze(doc);
  if(epoch!==generation)throw Object.assign(new Error('Document content changed'),{code:-32801});
  if(!proofReady)throw new Error('The pinned Lean 4.24 browser proof runtime is not installed yet or is still preparing. No proof has been claimed.');
  const key=JSON.stringify([epoch,doc.name,version,options]);
  emit('status',doc,{state:'running',functions:compiled.index.nodes.filter(n=>n.nodeType==='FunctionDefinition').map(n=>({range:compiled.index.nameRange(n),status:'running'})).filter(f=>f.range)});
  let report=proofCache.get(key),cacheHit=!!report;
  if(!report){
    const work=proofChain.then(async()=>{if(epoch!==generation)throw Object.assign(new Error('Document content changed'),{code:-32801});const job={epoch};activeProof=job;try{return await verifyInBrowser({compiled,text,name:doc.name,options,timeoutMs:settings.timeoutMs||600000});}finally{if(activeProof===job)activeProof=undefined;}});
    proofChain=work.catch(()=>{});try{report=await work;}catch(error){if(epoch===generation&&docs.get(doc.name)?.version===version){emit('status',doc,{state:error.code==='CANCELLED'?'cancelled':'error',functions:[]});if(error.code!=='CANCELLED'&&error.code!==-32801&&!error.preserveRuntime)resetProofs();}throw error;}
  }
  if(epoch!==generation||docs.get(doc.name)?.version!==version)throw Object.assign(new Error('Document content changed'),{code:-32801});
  proofCache.set(key,report);const full=options.function&&doc.report?{...report,results:[...doc.report.results.filter(old=>!report.results.some(row=>row.contract===old.contract&&(row.signature||row.function)===(old.signature||old.function))),...report.results]}:report;doc.report=full;
  emit('diagnostics',doc,{diagnostics:[...diagnostics(doc,compiled.diagnostics),...model.diagnostics(full).map(d=>({range:d.range,severity:d.severity==='error'?1:2,message:d.message,code:d.code,source:'Solidity Lean'}))]});
  emit('status',doc,{state:'complete',cacheHit,functions:full.results.map(row=>({range:model.rangeOf(row),status:row.status}))});
  emit('report',doc,{report,selection:options,cacheHit});return report;
}
function diagnostics(doc,rows){return rows.filter(d=>['error','warning'].includes(d.severity)).map(d=>{
  const other=d.sourceLocation?.file&&d.sourceLocation.file!==doc.name;
  const range=!other&&d.sourceLocation?.start>=0?language.byteRange(doc.text,`${d.sourceLocation.start}:${d.sourceLocation.end-d.sourceLocation.start}:0`):null;
  return {range:range||{start:{line:0,character:0},end:{line:0,character:0}},severity:d.severity==='error'?1:2,code:d.errorCode,source:'solc',message:d.formattedMessage||d.message};
});}
async function analyze(doc,overrides){
  await compilerReady;const version=doc.version,key=generation+':'+doc.name+':'+version+(overrides?':override':'');
  if(!overrides&&compiledCache.has(key))return compiledCache.get(key);
  emit('status',doc,{state:'compiling'});
  const text=overrides?.[doc.name]??doc.text;
  const source='/workspace/'+doc.name,all=snapshots().map(d=>overrides&&d.path.slice(11)in overrides?{...d,text:overrides[d.path.slice(11)]}:d);
  try{
    const project=projects.snapshot(source,text,{projectRoot:'/workspace'},all);
    compilations++;
    let compiled;try{compiled=compileFixture({args:['--source',source,'--out','/output/source.ast.json','--no-wrapper'],sourceBytes:new TextEncoder().encode(text),project,analysisOnly:true,quiet:true});}finally{globalThis.Module._solidity_reset();}
    const index=language.index(text,compiled.rawAst,{asts:compiled.rawAsts,files:project.files,uri:uri(doc.name)});
    const result={...compiled,index};
    if(!overrides){compiledCache.set(key,result);emit('diagnostics',doc,{diagnostics:diagnostics(doc,compiled.diagnostics)});emit('status',doc,{state:'ready',functions:index.nodes.filter(n=>n.nodeType==='FunctionDefinition').map(n=>({range:index.nameRange(n),status:'ready'})).filter(f=>f.range)});}
    return result;
  }catch(error){if(!overrides){emit('diagnostics',doc,{diagnostics:diagnostics(doc,error.diagnostics||[{severity:'error',message:error.message}])});emit('status',doc,{state:'error'});}throw error;}
}
function workspaceRoots(){return [...files.keys()].filter(p=>p.startsWith('/workspace/')&&p.endsWith('.sol')).map(p=>docs.get(p.slice(11))||{name:p.slice(11),text:readFileSync(p,'utf8'),version:0});}
const declarationIdentity=(index,node)=>{const location=index.location(node);return JSON.stringify([location?.uri,location?.range,node.nodeType,node.name]);};
async function referenceLocations(doc,index,target,include,strict){
  const identity=declarationIdentity(index,target),locations=[];
  for(const root of workspaceRoots()){
    let analyzed;try{analyzed=await analyze(root);}catch(error){if(strict)throw error;continue;}
    for(const declaration of analyzed.index.declarations.values())if(declarationIdentity(analyzed.index,declaration)===identity)locations.push(...analyzed.index.locations(declaration,include));
  }
  return [...new Map(locations.map(l=>[JSON.stringify([l.uri,l.range]),l])).values()];
}
function schedule(doc){
  clearTimeout(doc.timer);doc.timer=setTimeout(async()=>{if(docs.get(doc.name)!==doc)return;try{await analyze(doc);if(settings.automaticVerification==='change'&&proofReady)await verify(doc,{auditPreconditions:settings.auditPreconditions,counterexamples:settings.counterexamples});}catch(error){if(error.code!==-32801&&error.code!=='CANCELLED')send('log',{message:error.message});}},150);
}
async function service(method,p){
  if(method==='workspace'){
    const entries=Object.entries(p.files||{});for(const [name,text]of entries){if(!validName(name)||typeof text!=='string'||new TextEncoder().encode(text).length>8*1024*1024)throw new Error('Invalid workspace snapshot');}
    const projected=new Map([...files].filter(([name])=>name.startsWith('/workspace/')));for(const [name,text]of entries)projected.set('/workspace/'+name,text);
    if(projected.size>128||[...projected.values()].reduce((sum,text)=>sum+(typeof text==='string'?new TextEncoder().encode(text).length:text.length),0)>32*1024*1024)throw new Error('Workspace exceeds 128 files or 32 MiB');
    let changed=false;for(const [name,text]of entries){const path='/workspace/'+name;if(!files.has(path)||readFileSync(path,'utf8')!==text){writeFileSync(path,text);if(docs.get(name)?.text!==text)changed=true;}}
    if(changed)invalidate();return {updated:entries.length};
  }
  if(method==='open'||method==='change'){
    if(!validName(p.name)||typeof p.text!=='string'||new TextEncoder().encode(p.text).length>8*1024*1024||!Number.isSafeInteger(p.version)||p.version<1)throw new Error('Invalid document');
    const old=docs.get(p.name);if(old&&p.version<=old.version)throw new Error('Document version must increase');if(!old&&docs.size>=4)throw new Error('Maximum four open documents');
    clearTimeout(old?.timer);const doc={name:p.name,text:p.text,version:p.version};docs.set(p.name,doc);invalidate();
    schedule(doc);
    return {uri:uri(p.name),version:p.version};
  }
  if(method==='close'){const doc=document(p.name);clearTimeout(doc.timer);writeFileSync('/workspace/'+doc.name,doc.text);docs.delete(p.name);invalidate();return null;}
  if(method==='save'){const doc=document(p.name);writeFileSync('/workspace/'+doc.name,doc.text);if(settings.automaticVerification==='save'&&proofReady)verify(doc,{auditPreconditions:settings.auditPreconditions,counterexamples:settings.counterexamples}).catch(error=>send('log',{message:error.message}));return {saved:true};}
  if(method==='configure'){if(!['never','change','save'].includes(p.automaticVerification??'never'))throw new Error('Invalid automatic verification setting');if(p.timeoutMs!==undefined&&(!Number.isSafeInteger(p.timeoutMs)||p.timeoutMs<1||p.timeoutMs>3600000))throw new Error('Invalid verification timeout');settings={...settings,...p,workers:1};invalidate();if(settings.automaticVerification==='change')for(const doc of docs.values())schedule(doc);return settings;}
  if(method==='restart'){resetProofs(true);invalidate();return {restarted:true};}
  if(method==='cancel'){resetProofs();invalidate();for(const doc of docs.values())if(!p.name||p.name===doc.name){clearTimeout(doc.timer);emit('status',doc,{state:'cancelled'});}return null;}
  if(method==='stats')return {runtime:'browser',documents:docs.size,compilerReady:true,proofReady,compilations};
  if(method==='verify')return verify(document(p.name,p.version),{listing:!!p.listing,benchmark:!!p.benchmark,contract:p.contract,function:p.function,auditPreconditions:p.auditPreconditions??settings.auditPreconditions,certify:p.certify,counterexamples:p.counterexamples??settings.counterexamples});
  if(method==='workspace/symbol'){const results=[];for(const doc of workspaceRoots()){let c;try{c=await analyze(doc);}catch{continue;}const walk=rows=>{for(const s of rows){if(s.name.toLowerCase().includes(String(p.query||'').toLowerCase()))results.push({name:s.name,kind:s.kind,location:{uri:uri(doc.name),range:s.selectionRange}});walk(s.children||[]);}};walk(c.index.symbols);}return results;}
  const doc=document(p.name,p.version);let compiled;try{compiled=await analyze(doc);}catch(error){if(method!=='textDocument/completion')throw error;}
  const index=compiled?.index;
  if(method==='textDocument/documentSymbol')return index?.symbols||[];
  if(method==='textDocument/completion')return language.completion(doc.text,p.position,index);
  if(method==='textDocument/signatureHelp')return language.signatureHelp(doc.text,p.position,index);
  if(method==='textDocument/formatting'){
    const formatted=textTools.format(doc.text,p.options);if(formatted===doc.text)return [];
    const checked=await analyze(doc,{[doc.name]:formatted});
    const attachments=ast=>{const result=[];const walk=n=>{if(!n||typeof n!=='object')return;if(n.nodeType&&(n.documentation?.text||n.loopSpec))result.push([n.nodeType,n.documentation?.text,n.loopSpec]);for(const child of Object.values(n))if(child&&typeof child==='object'){if(Array.isArray(child))child.forEach(walk);else walk(child);}};walk(ast);return JSON.stringify(result);};
    if(attachments(compiled.annotationAst)!==attachments(checked.annotationAst))throw new Error('Formatting would change specification attachment');
    return [{range:{start:{line:0,character:0},end:language.position(doc.text,doc.text.length)},newText:formatted}];
  }
  if(method==='textDocument/codeAction')return (p.context?.diagnostics||[]).filter(d=>String(d.code)==='1878').flatMap(d=>['UNLICENSED','MIT','Apache-2.0'].map(license=>({title:'Add SPDX license identifier: '+license,kind:'quickfix',edit:{documentChanges:[{textDocument:{uri:uri(doc.name),version:doc.version},edits:[{range:{start:{line:0,character:0},end:{line:0,character:0}},newText:'// SPDX-License-Identifier: '+license+'\n'}]}]}})));
  const occurrence=index?.occurrence(p.position),target=occurrence?.declaration;
  if(method==='textDocument/hover'){const rows=doc.report?.results.filter(row=>language.contains(model.rangeOf(row),p.position)),row=rows?.find(r=>r.sourceId>=0)||rows?.[0];if(row)return {contents:{kind:'plaintext',value:model.detail(row)},range:model.rangeOf(row)};return target?{contents:{kind:'plaintext',value:`${target.name||target.kind}: ${target.typeDescriptions?.typeString||target.nodeType}`},range:occurrence.range}:null;}
  if(!target)return ['textDocument/references','textDocument/documentHighlight'].includes(method)?[]:null;
  if(method==='textDocument/definition'){const l=index.location(target);return {uri:l.uri||uri(doc.name),range:l.range};}
  if(method==='textDocument/prepareRename')return {range:occurrence.range,placeholder:target.name};
  const locations=await referenceLocations(doc,index,target,p.context?.includeDeclaration??true,method==='textDocument/rename');
  if(method==='textDocument/references')return locations.map(l=>({uri:l.uri||uri(doc.name),range:l.range}));
  if(method==='textDocument/documentHighlight')return locations.filter(l=>(l.uri||uri(doc.name))===uri(doc.name)).map(l=>({range:l.range,kind:1}));
  if(method==='textDocument/rename'){
    if(!language.validIdentifier(p.newName))throw new Error('Invalid Solidity identifier');
    if([...index.declarations.values()].some(n=>n.id!==target.id&&n.name===p.newName))throw new Error('Rename would collide with an existing declaration');
    const word=new RegExp(`(?<![\\w$])${target.name.replace(/[.*+?^${}()|[\]\\]/g,'\\$&')}(?![\\w$])`);
    if(index.allNodes.some(n=>typeof n.documentation?.text==='string'&&word.test(n.documentation.text)))throw new Error('Rename involving specification text requires a manual specification update');
    const groups=new Map();for(const l of locations){const u=l.uri||uri(doc.name);if(!groups.has(u))groups.set(u,{textDocument:{uri:u,version:l.version??null},edits:[]});groups.get(u).edits.push({range:l.range,newText:p.newName});}
    const overrides={};for(const [u,change]of groups){const name=decodeURIComponent(u.split('/').pop()),text=docs.get(name)?.text??readFileSync('/workspace/'+name,'utf8');overrides[name]=language.applyChanges(text,[...change.edits].sort((a,b)=>language.offset(text,b.range.start)-language.offset(text,a.range.start)).map(e=>({range:e.range,text:e.newText})));}
    // Recompile every root against all edited files before returning a rename.
    const backup=new Map();try{for(const [name,text]of Object.entries(overrides)){const file='/workspace/'+name;backup.set(file,files.get(file));writeFileSync(file,text);}for(const root of workspaceRoots())await analyze(root,overrides);}finally{for(const [file,text]of backup)if(text)files.set(file,text);else files.delete(file);}
    return {documentChanges:[...groups.values()]};
  }
  throw new Error('Browser method not supported: '+method);
}
compilerReady=loadCompiler();
compilerReady.then(()=>postMessage({method:'workerReady'})).catch(error=>send('backendError',{message:error.message}));
let mutations=Promise.resolve();const mutating=new Set(['workspace','open','change','close','save','configure','restart']);
onmessage=async event=>{const {id,method,params={}}=event.data;try{if(!Number.isSafeInteger(id))throw new Error('Invalid request');let result;if(mutating.has(method)){const action=mutations.then(()=>service(method,params));mutations=action.catch(()=>{});result=await action;}else{await mutations;result=await service(method,params);}postMessage({id,result});}catch(error){postMessage({id,error:{message:error.message,code:error.code||-32602}});}};
