// Native workspace-symbol API/LSP observations; no rendered search or proof claim.
'use strict';
const fs=require('node:fs'),path=require('node:path'),assert=require('node:assert/strict');
const {createHash}=require('node:crypto'),{pathToFileURL}=require('node:url');
const queries=['f0','__parity_missing_symbol__','f0'];
const hash=text=>createHash('sha256').update(text).digest('hex');
function normalize(rows,uri,api=false){
 assert.ok(Array.isArray(rows),'Missing workspace symbol array');
 return rows.map(row=>{
  const location=row.location,range=location?.range;
  assert.equal(api?location?.uri?.toString():location?.uri,uri,'Foreign workspace symbol');
  assert.ok(require('../src/model.cjs').validRange(range),'Unresolved/invalid symbol range');
  assert.ok(typeof row.name==='string'&&Number.isSafeInteger(row.kind));
  return{name:row.name,kind:row.kind+(api?1:0),range:{start:{line:range.start.line,character:range.start.character},end:{line:range.end.line,character:range.end.character}}};
 });
}
function requests(protocol){
 const pending=new Map(),seen=new Set(),rows=[];
 for(const [index,record]of protocol.entries()){
  assert.ok(!record.error,'Protocol framing failed');const m=record.message;
  if(record.direction==='client'&&m?.method==='workspace/symbol'){
   assert.ok(typeof record.processSession==='string'&&record.processSession);
   assert.ok(typeof m.id==='string'&&m.id||Number.isSafeInteger(m.id));
   const key=JSON.stringify([record.processSession,m.id]);assert.ok(!seen.has(key),'Reused workspace request identity');seen.add(key);
   const row={requestIndex:index,request:record};pending.set(key,row);rows.push(row);
  }else if(record.direction==='server'&&m&&!m.method){
   const key=JSON.stringify([record.processSession,m.id]),row=pending.get(key);
   if(seen.has(key)){assert.ok(row,'Duplicate workspace response');row.responseIndex=index;row.response=record;pending.delete(key);}
  }
 }
 return rows;
}
function readinessRecord(protocol,target,binding){
 return protocol.findIndex(r=>r.direction==='server'&&r.message?.params?.uri===binding.uri&&r.message.params.version===binding.version&&
  (target==='local'?r.message.method==='solidityLean/status'&&r.message.params.state==='ready'&&r.message.params.sourceHash===binding.sourceHash:r.message.method==='dafny/compilation/status'&&r.message.params.status==='ResolutionSucceeded'));
}
async function waitForCompilation(read,target,binding,timeoutMs,observation,{now=()=>require('node:perf_hooks').performance.now(),delay=ms=>new Promise(resolve=>setTimeout(resolve,ms))}={}){
 assert.ok(Number.isSafeInteger(timeoutMs)&&timeoutMs>0);const started=now(),deadline=started+timeoutMs;
 Object.assign(observation,{status:'waiting',binding,started,deadline,timeoutMs});
 const expired=()=>Object.assign(Error('Timed out: current source compilation readiness'),{code:'TIMEOUT'});
 try{while(true){
  const before=now();if(before>=deadline)throw expired();observation.lastSample={before};
  const protocol=read(),index=readinessRecord(protocol,target,binding),after=now();
  observation.lastSample={before,after,index,record:index>=0?protocol[index]:null};
  if(after>=deadline)throw expired();
  if(index>=0){Object.assign(observation,{status:'observed',index,record:protocol[index],finished:after});return;}
  await delay(Math.min(20,deadline-after));
 }}catch(error){Object.assign(observation,{status:error.code==='TIMEOUT'?'timeout':'failed',finished:now(),error:error.stack});throw error;}
}
function readinessErrors(o,config,owner){
 const ready=o.readiness;assert.equal(o.stage,'after-resolution');assert.equal(ready?.status,'observed');assert.ok(!ready.error);assert.deepEqual(ready.binding,o.rows[0].binding);assert.ok(ready&&Number.isSafeInteger(ready.index)&&ready.index>=0&&ready.index<o.rows[0].start,'Missing actual readiness before query');
 assert.ok([ready.started,ready.deadline,ready.finished,ready.lastSample?.before,ready.lastSample?.after].every(Number.isFinite));assert.equal(ready.timeoutMs,config.operationTimeoutMs);assert.equal(ready.deadline,ready.started+ready.timeoutMs);assert.ok(ready.lastSample.before>=ready.started&&ready.lastSample.after>=ready.lastSample.before&&ready.finished===ready.lastSample.after&&ready.finished<ready.deadline,'Late readiness refused');assert.equal(ready.lastSample.index,ready.index);assert.deepEqual(ready.lastSample.record,ready.record);
 const record=o.protocol[ready.index];assert.deepEqual(ready.record,record);assert.equal(readinessRecord(o.protocol.slice(0,ready.index+1),config.target,o.rows[0].binding),ready.index);
 for(const key of ['processSession','pid','birth','processSequence'])assert.equal(record[key],owner[key],'Foreign readiness process');
 const uri=o.rows[0].binding.uri,own=o.protocol.slice(0,ready.index+1).filter(r=>r.processSession===owner.processSession),wire=require('./trace-presentation.cjs').wireDocument(own,own.length,uri);
 assert.equal(wire.version,o.rows[0].binding.version);assert.equal(wire.textHash,o.rows[0].binding.sourceHash);
 assert.ok(!o.protocol.slice(ready.index+1,o.rows.at(-1).end).some(r=>r.processSession===owner.processSession&&r.direction==='client'&&['textDocument/didOpen','textDocument/didChange','textDocument/didClose'].includes(r.message?.method)&&r.message.params.textDocument.uri===uri),'Source lifetime changed after readiness');
}
function errors(o,config){try{
 assert.ok(['local','dafny'].includes(config.target));assert.match(config.sourceHead,/^[a-f0-9]{40}$/);
 assert.equal(o.runId,config.runId);assert.equal(o.target,config.target);assert.equal(o.sourceHead,config.sourceHead);
 assert.equal(o.origin,'native public workspace symbol API + owned LSP');
 assert.ok(!o.error&&!o.protocolError&&!o.reportingError&&!o.sourceError);assert.ok(o.validationErrors===undefined||Array.isArray(o.validationErrors)&&o.validationErrors.length===0);
 const source=require('./workloads.cjs').workload(config.target,1),uri=pathToFileURL(path.join(config.workspace,'workspace-symbols.'+(config.target==='local'?'sol':'dfy'))).href;
 assert.equal(o.source,source);assert.equal(o.diskHash,hash(source));assert.deepEqual(o.rows.map(r=>r.query),queries);
 const records=requests(o.protocol);assert.equal(records.length,3,'Unexpected workspace request count');let last=0,owner,session,version;
 for(const row of o.rows){
  const b=row.binding;assert.equal(b.uri,uri);assert.equal(b.sourceHash,hash(source));assert.equal(b.language,config.target==='local'?'solidity':'dafny');assert.equal(b.trusted,true);assert.ok(Number.isSafeInteger(b.version)&&b.version>=1);assert.ok(typeof b.session==='string'&&b.session);session??=b.session;version??=b.version;assert.equal(b.session,session);assert.equal(b.version,version);assert.deepEqual(row.after,b);
  assert.ok(Number.isSafeInteger(row.start)&&Number.isSafeInteger(row.end)&&row.start>=last&&row.end>=row.start&&row.end<=o.protocol.length);last=row.end;
  assert.equal(row.apiReturnType,'array');assert.deepEqual(normalize(row.apiValues,uri),row.symbols);assert.ok(Array.isArray(row.rawApiValue)&&row.rawApiValue.length===row.apiValues.length);for(let i=0;i<row.apiValues.length;i++){assert.equal(row.rawApiValue[i].name,row.apiValues[i].name);assert.equal(row.rawApiValue[i].kind+1,row.apiValues[i].kind);}
  const matches=records.filter(r=>r.requestIndex>=row.start&&r.requestIndex<row.end);assert.equal(matches.length,1,'One owned workspace request per API interval');
  const r=matches[0],processSession=r.request.processSession,identity={processSession,pid:r.request.pid,birth:r.request.birth,processSequence:r.request.processSequence};assert.ok(Number.isSafeInteger(identity.pid)&&identity.pid>0&&typeof identity.birth==='string'&&/^\d+$/.test(identity.birth)&&Number.isSafeInteger(identity.processSequence)&&identity.processSequence>0);owner??=identity;assert.deepEqual(identity,owner,'Workspace server epoch changed');assert.equal(r.request.message.params.query,row.query);
  assert.ok(r.response&&r.responseIndex<row.end&&!r.response.message.error,'Missing timely owned response');for(const key of ['pid','birth','processSequence'])assert.equal(r.response[key],identity[key]);assert.deepEqual(normalize(r.response.message.result,uri),row.symbols);
  const own=o.protocol.slice(0,r.requestIndex).filter(v=>v.processSession===processSession),wire=require('./trace-presentation.cjs').wireDocument(own,own.length,uri);
  assert.equal(wire.version,b.version);assert.equal(wire.textHash,b.sourceHash);assert.equal(own[wire.openIndex].message.params.textDocument.languageId,b.language);
  const lines=source.split('\n');for(const symbol of row.symbols)for(const point of [symbol.range.start,symbol.range.end])assert.ok(point.line<lines.length&&point.character<=lines[point.line].replace(/\r$/,'').length,'Symbol range outside source');
  assert.ok(!o.protocol.slice(r.requestIndex,row.end).some(v=>v.processSession===processSession&&v.direction==='client'&&['textDocument/didOpen','textDocument/didChange','textDocument/didClose'].includes(v.message?.method)&&v.message.params.textDocument.uri===uri),'Workspace query crossed source lifetime');
  if(row.query==='f0')assert.ok(row.symbols.some(s=>/(?:^|\.)f0(?:\(|$)/.test(s.name)),'Missing actual function symbol');else assert.deepEqual(row.symbols,[]);
 }
 if(config.suite==='workspace-symbols-resolved')readinessErrors(o,config,owner);else assert.ok(o.stage===undefined||o.stage==='immediate','Foreign observation stage');
 assert.deepEqual(o.restored,o.rows.at(-1).binding);
 assert.ok(!o.protocol.some(r=>r.direction==='client'&&['solidityLean/verify','dafny/verify','dafny/textDocument/verify','workspace/executeCommand'].includes(r.message?.method)),'Unexpected proof/action request');
 return[];
 }catch(error){return['Incomplete native workspace symbol evidence: '+error.message];}}
async function run({vscode,config,events,sessionFor,bounded}){
 const source=require('./workloads.cjs').workload(config.target,1),file=path.join(config.workspace,'workspace-symbols.'+(config.target==='local'?'sol':'dfy'));
 const result={stage:config.suite==='workspace-symbols-resolved'?'after-resolution':'immediate',status:'partial',origin:'native public workspace symbol API + owned LSP',runId:config.runId,target:config.target,sourceHead:config.sourceHead,source,rows:[],scope:'API/LSP only; no rendered search, cancellation UI, glyph, proof or semantic parity.'};let doc,failure;const begin=events.length;
 const save=()=>fs.writeFileSync(path.join(config.dir,'workspace-symbol-observations.json'),JSON.stringify(result,null,2));
 const wire=()=>fs.readFileSync(config.trace,'utf8').trim().split('\n').filter(Boolean).map(JSON.parse);
 const binding=()=>{assert.ok(doc&&!doc.isClosed&&vscode.workspace.textDocuments.includes(doc)&&vscode.window.activeTextEditor?.document===doc);return{uri:doc.uri.toString(),version:doc.version,sourceHash:hash(doc.getText()),session:sessionFor(doc),language:doc.languageId,trusted:vscode.workspace.isTrusted};};
 try{
  fs.writeFileSync(file,source,{flag:'wx'});doc=await bounded(vscode.workspace.openTextDocument(file),'workspace source open');await bounded(vscode.window.showTextDocument(doc,{preview:false}),'workspace source show');
  if(result.stage==='after-resolution'){const before=binding();result.readiness={status:'waiting',binding:before};save();await waitForCompilation(wire,config.target,before,config.operationTimeoutMs,result.readiness);assert.deepEqual(binding(),before);save();}
  for(const query of queries){const row={query,binding:binding(),start:wire().length};result.rows.push(row);save();const values=await bounded(vscode.commands.executeCommand('vscode.executeWorkspaceSymbolProvider',query),'workspace symbols '+query);row.apiReturnType=Array.isArray(values)?'array':values===undefined?'undefined':values===null?'null':typeof values;
   row.rawApiValue=require('./code-action-lifecycle.cjs').argumentSnapshot(values);row.apiValues=Array.isArray(values)?values.map(v=>({name:v.name,kind:v.kind+1,location:{uri:v.location?.uri?.toString(),range:v.location?.range&&{start:{line:v.location.range.start.line,character:v.location.range.start.character},end:{line:v.location.range.end.line,character:v.location.range.end.character}}}})):require('./code-action-lifecycle.cjs').argumentSnapshot(values);
   row.symbols=Array.isArray(values)?normalize(values,doc.uri.toString(),true):null;row.after=binding();row.end=wire().length;save();
  }
 }catch(error){failure=error;result.error=error.stack;}
 finally{
  try{result.restored=binding();result.diskHash=hash(fs.readFileSync(file));assert.equal(doc.getText(),source);assert.equal(result.diskHash,hash(source));}catch(error){result.sourceError=error.stack;failure??=error;}
  try{result.protocol=wire();}catch(error){result.protocolError=error.message;failure??=error;}
  result.events=events.slice(begin);if(!failure){result.validationErrors=errors(result,config);if(result.validationErrors.length)failure=Error(result.validationErrors.join('; '));}
  try{save();}catch(error){result.reportingError=error.message;failure??=error;}
 }
 if(failure)throw Object.assign(failure,{observation:result});return result;
}
module.exports={run,errors,normalize,requests,readinessRecord,waitForCompilation};
