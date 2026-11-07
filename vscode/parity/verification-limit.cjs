// Native configuration/transport observations; never a proof-timeout equivalence claim.
'use strict';
const fs=require('node:fs'),path=require('node:path'),{randomUUID,createHash}=require('node:crypto');
const {workload,symbolPosition}=require('./workloads.cjs');
const digest=s=>createHash('sha256').update(s).digest('hex');
const key=target=>target==='dafny'?'verificationTimeLimit':'timeoutMs',section=target=>target==='dafny'?'dafny':'solidityLean';
function launchSettings(settings,target,suite){if(suite==='verification-time-limit'){delete settings['dafny.verificationTimeLimit'];delete settings['solidityLean.timeoutMs'];}return settings;}
function records(file){return fs.existsSync(file)?fs.readFileSync(file,'utf8').split('\n').filter(Boolean).map(JSON.parse):[];}
function serverProcesses(events,target){return events.filter(e=>e.kind==='process.spawn'&&e.data.args?.some(a=>typeof a==='string'&&(target==='local'?a.endsWith('lsp-server.cjs'):a==='server')));}
function hoverText(value){if(typeof value==='string')return value;if(Array.isArray(value))return value.map(hoverText).join('\n');if(value&&typeof value.value==='string')return value.value;return '';}
async function withinOperation(operation,timeoutMs,label,{now=()=>require('node:perf_hooks').performance.now(),setTimer=setTimeout,clearTimer=clearTimeout}={}){
 if(typeof operation!=='function'||!Number.isSafeInteger(timeoutMs)||timeoutMs<1)throw Error('Invalid original operation deadline');
 const deadline=now()+timeoutMs,expired=()=>Object.assign(Error('Timed out: '+label),{code:'TIMEOUT'});let timer;
 try{const timeout=new Promise((_,reject)=>{timer=setTimer(()=>reject(expired()),timeoutMs);});const value=await Promise.race([Promise.resolve().then(operation),timeout]);if(now()>=deadline)throw expired();return value;}finally{clearTimer(timer);}
}
function errors(o,runId,expectedOuterTimeoutMs){
 const e=[];if(!o||o.runId!==runId||!['dafny','local'].includes(o.target)||!Array.isArray(o.cases)||o.cases.length!==3)return['missing time-limit cases'];
 const full=section(o.target)+'.'+key(o.target),nativeDefault=o.target==='dafny'?'20':600000;
 if(Object.hasOwn(o.launch?.settings||{},full))e.push('harness override cannot evidence a native default');
 if(!Number.isSafeInteger(o.outerTimeoutMs)||o.outerTimeoutMs<1||o.launch?.suite!=='verification-time-limit'||o.outerTimeoutMs!==o.launch?.outerOperationTimeoutMs||expectedOuterTimeoutMs!==undefined&&o.outerTimeoutMs!==expectedOuterTimeoutMs)e.push('missing original outer guard');
 let previous;
 for(const [i,c]of o.cases.entries()){
  if(c.id!==['native-default','finite-2','finite-3'][i]||c.configuration?.effective!==(i?(o.target==='dafny'?i+1:(i+1)*1000):nativeDefault)||c.configuration?.inspect?.defaultValue!==nativeDefault)e.push('wrong raw effective/default value');
  if(!i&&['globalValue','workspaceValue','workspaceFolderValue'].some(k=>c.configuration?.inspect?.[k]!==undefined))e.push('explicit value masquerades as default');
  if(i&&c.configuration?.inspect?.workspaceValue!==(o.target==='dafny'?i+1:(i+1)*1000))e.push('missing explicit workspace configuration');
  if(c.source?.uri!==o.uri||c.source?.textHash!==digest(o.source||'')||!c.source?.session||c.source?.closed||!c.source?.trusted||!Number.isInteger(c.source?.version))e.push('wrong source ownership');
  if(!c.process?.processSession||!/^\d+$/.test(c.process.birth||'')||!Number.isInteger(c.process.pid)||c.process.processSession===previous)e.push('missing fresh actual process identity');previous=c.process?.processSession;
  const launch=c.process?.args||[];
  if(o.target==='dafny'&&!launch.includes('--verification-time-limit:'+String(c.configuration?.effective)))e.push('missing actual Dafny launch argument');
  if(c.protocol?.some(r=>r.processSession!==c.process?.processSession||r.pid!==c.process?.pid||r.birth!==c.process?.birth))e.push('foreign protocol process identity');
  const init=c.protocol?.find(r=>r.direction==='client'&&r.message?.method==='initialize');
  if(!init||init.processSession!==c.process?.processSession||!c.protocol?.some(r=>r.processSession===init.processSession&&r.direction==='server'&&r.message?.id===init.message.id&&r.message.result))e.push('missing matching native initialization');
  if(o.target==='local'&&init?.message?.params?.initializationOptions?.settings?.timeoutMs!==c.configuration?.effective)e.push('wrong local initialization timeout');
  const open=c.protocol?.find(r=>r.direction==='client'&&r.processSession===c.process?.processSession&&r.message?.method==='textDocument/didOpen'&&r.message.params?.textDocument?.uri===o.uri);
  if(open?.message.params.textDocument.version!==c.source?.version||digest(open?.message.params.textDocument.text||'')!==c.source?.textHash)e.push('missing exact current wire open');
  if(!c.query||c.query.uri!==o.uri||c.query.sourceHash!==c.source?.textHash||c.query.status!=='resolved'||!c.query.nonempty||c.query.version!==c.source?.version||!Array.isArray(c.query.value)||!c.query.value.length||!c.query.value.every(h=>hoverText(h?.contents).length>0))e.push('missing actual current language response');
  if(i&&(!c.retired?.some(r=>r.processSession===o.cases[i-1]?.process?.processSession&&r.birth===o.cases[i-1]?.process?.birth&&r.closedMs<=c.process?.spawnedMs)||!c.restart?.finished))e.push('missing old root close/restart');
  const request=c.query?.wire?.find(r=>r.direction==='client'&&r.processSession===c.process?.processSession&&r.message?.method==='textDocument/hover'&&r.message.params?.textDocument?.uri===o.uri);
  const response=c.query?.wire?.find(r=>r.direction==='server'&&r.processSession===c.process?.processSession&&r.message?.id===request?.message.id);
  const apiText=Array.isArray(c.query?.value)?c.query.value.map(h=>hoverText(h.contents)).join('\n'):'';
  if(!request||!response||!hoverText(response.message?.result?.contents)||apiText!==hoverText(response.message?.result?.contents)||request.message.params.textDocument.version!==undefined&&request.message.params.textDocument.version!==c.source?.version||JSON.stringify(request.message.params.position)!==JSON.stringify(c.query.position)||JSON.stringify(c.query.position)!==JSON.stringify(symbolPosition(o.target,o.source))||JSON.stringify(c.query.before)!==JSON.stringify(c.source)||JSON.stringify(c.query.after)!==JSON.stringify(c.source)||c.query.before?.version!==c.source?.version||c.query.before?.textHash!==c.source?.textHash||c.query.wire.some(r=>r.processSession!==c.process?.processSession||r.pid!==c.process?.pid||r.birth!==c.process?.birth))e.push('missing current request/response identity');
 }
 if(o.target==='local'&&(o.cases[0]?.preCancelled?.status!=='rejected'||o.cases[0].preCancelled.code!==-32800||o.cases[0].preCancelled.wire?.some(r=>r.message?.method==='textDocument/hover')))e.push('missing actual pre-cancel refusal');
 if(!o.restoration?.confirmed||JSON.stringify(o.restoration.expected)!==JSON.stringify(o.restoration.actual)||JSON.stringify(JSON.parse(o.restoration.rawBefore))!==JSON.stringify(JSON.parse(o.restoration.rawAfter)))e.push('owned setting restoration missing');
 if(o.unlimitedTested!==false||o.proofTimeoutEstablished!==false)e.push('unsupported unlimited/proof claim');
 return e;
}
async function run({vscode,config,api,events,until}){
 const target=config.target,sec=section(target),setting=key(target),uri=vscode.Uri.file(path.join(config.workspace,'time-limit'+(target==='dafny'?'.dfy':'.sol'))),source=workload(target,1),session=randomUUID(),settingsFile=path.join(config.workspace,'.vscode/settings.json');
 const cfg=()=>vscode.workspace.getConfiguration(sec,target==='local'?uri:undefined),inspect=()=>cfg().inspect(setting),before=inspect().workspaceValue,rawBefore=fs.readFileSync(settingsFile,'utf8');
 const o={runId:config.runId,target,uri:uri.toString(),source,launch:config.verificationLimitLaunch,outerTimeoutMs:config.operationTimeoutMs,cases:[],unlimitedTested:false,proofTimeoutEstablished:false,limitations:['Different units, defaults and scope; native APIs/wire only, no rendered-settings claim.','No infinite or proof-timeout workload; local requests use native compiler services only.','Pending query may finish before change; cancellation/stale coverage reported only as observed.']};
 let doc;
 const binding=()=>({uri:doc.uri.toString(),version:doc.version,textHash:digest(doc.getText()),session,closed:doc.isClosed,trusted:vscode.workspace.isTrusted});
 const save=()=>fs.writeFileSync(path.join(config.dir,'verification-time-limit-observations.json'),JSON.stringify(o,null,2));
 const query=async()=>{const b=binding(),position=symbolPosition(target,source),started=Date.now(),wireStart=records(config.trace).length;try{const value=await withinOperation(()=>vscode.commands.executeCommand('vscode.executeHoverProvider',uri,new vscode.Position(position.line,position.character)),config.operationTimeoutMs,'time-limit hover');return{uri:b.uri,sourceHash:b.textHash,version:b.version,position,before:b,after:binding(),started,finished:Date.now(),status:'resolved',nonempty:Array.isArray(value)&&value.length>0,value,wire:records(config.trace).slice(wireStart)};}catch(error){return{uri:b.uri,sourceHash:b.textHash,version:b.version,started,finished:Date.now(),status:'rejected',code:error.code,message:error.message};}};
 try{
  fs.writeFileSync(uri.fsPath,source);doc=await vscode.workspace.openTextDocument(uri);await vscode.window.showTextDocument(doc,{preview:false});
  for(let i=0;i<3;i++){
   const start=events.length,restart={started:Date.now()};
   let pending;
   if(i){pending=query();await withinOperation(()=>cfg().update(setting,target==='dafny'?i+1:(i+1)*1000,vscode.ConfigurationTarget.Workspace),config.operationTimeoutMs,'finite setting update');await withinOperation(()=>vscode.commands.executeCommand(target==='dafny'?'dafny.restartServer':'solidityLean.restartServer'),config.operationTimeoutMs,'time-limit restart');}
   await until(()=>{const ps=serverProcesses(events,target),p=ps.at(-1)?.data;return p&&records(config.trace).some(r=>r.processSession===p.processSession&&r.message?.method==='textDocument/didOpen'&&r.message.params?.textDocument?.uri===uri.toString());},'actual current process open');
   const spawn=serverProcesses(events,target).at(-1),process={...spawn.data,spawnedMs:spawn.ms},protocol=records(config.trace).filter(r=>r.processSession===process.processSession);restart.finished=Date.now();
   const c={id:['native-default','finite-2','finite-3'][i],configuration:{effective:cfg().get(setting),inspect:inspect(),resource:target==='local'?uri.toString():null},source:binding(),process,protocol,restart,retired:events.slice(start).filter(e=>e.kind==='process.close').map(e=>({...e.data,closedMs:e.ms})),query:await query()};
   if(pending)c.queryAcrossConfiguration=await pending;
   if(!i&&target==='local'){
    const controller=new AbortController();controller.abort();const wireStart=records(config.trace).length,started=Date.now();
    try{await withinOperation(()=>api.service.request('textDocument/hover',doc,{position:symbolPosition(target,source)},{signal:controller.signal}),config.operationTimeoutMs,'pre-cancelled hover');c.preCancelled={started,finished:Date.now(),status:'resolved',aborted:true};}
    catch(error){c.preCancelled={started,finished:Date.now(),status:'rejected',code:error.code,message:error.message,aborted:true};}
    c.preCancelled.wire=records(config.trace).slice(wireStart);
   }
   o.cases.push(c);save();
  }
 }catch(error){o.error=error.stack;error.observation=o;throw error;}
 finally{
  try{await withinOperation(()=>cfg().update(setting,before,vscode.ConfigurationTarget.Workspace),config.operationTimeoutMs,'owned setting restoration');const actual=inspect().workspaceValue;const rawAfter=fs.readFileSync(settingsFile,'utf8');o.restoration={expected:before,actual,confirmed:JSON.stringify(actual)===JSON.stringify(before),rawBefore,rawAfter};}catch(error){o.restoration={confirmed:false,error:error.message};}
  save();
 }
 const failed=errors(o,config.runId,config.operationTimeoutMs);if(failed.length){const error=Error(failed.join('; '));error.observation=o;throw error;}
 return{...o,status:'partial'};
}
const safeErrors=(o,id,timeout)=>{try{return errors(o,id,timeout);}catch{return['malformed time-limit observation'];}};
module.exports={launchSettings,errors:safeErrors,run,serverProcesses,withinOperation};
