'use strict';
// Two persistent language servers. Fresh declarations force real verification;
// no cached-report retrieval is included in the warm verification medians.
const fs=require('node:fs'),path=require('node:path'),assert=require('node:assert/strict'),{spawn}=require('node:child_process'),{pathToFileURL}=require('node:url'),{createHash}=require('node:crypto');
const {RpcPeer}=require('../src/rpc.cjs');
const root=path.resolve(__dirname,'../..'),dafny=process.env.DAFNY;
if(!dafny)throw new Error('Set DAFNY to the pinned 4.11.0 executable');
const z3=process.env.DAFNY_Z3||path.join(path.dirname(dafny),'z3/bin/z3-4.12.1');
const directory=fs.mkdtempSync(path.join(root,'.lake/compiled-comparison-')),limit=(1n<<256n).toString(),max=((1n<<256n)-1n).toString(),R='\\result';
const cases=[
 ['constant','',`${R} == 1`,'return 1;','','r == 1','r := 1;'],
 ['identity','uint x',`${R} == x`,'return x;','x:int','r == x','r := x;'],
 ['assignment','uint x','value == x','value = x;','value:int, x:int','r == x','r := x;'],
 ['increment','','value == \\old(value) + 1','value = value + 1;','value:int','r == value + 1','r := value + 1;'],
 ['branch','uint x, uint y',`${R} >= x`,'if (x >= y) return x; else return y;','x:int, y:int','r >= x','if x >= y { r := x; } else { r := y; }'],
 ['false-constant','',`${R} == 1`,'return 2;','','r == 1','r := 2;']
];
const report={startedAt:new Date().toISOString(),scope:'Fresh document submission to completed verification in two persistent language servers; fresh method names, one worker/core. Dafny verification cache disabled. Scalar examples only; languages and verification algorithms differ. The increment Dafny input excludes overflowing entries which Solidity reverts from.',trials:[]};
async function server(command,args){
 const child=spawn(command,args,{cwd:directory,stdio:['pipe','pipe','pipe']});let stderr='';child.stderr.on('data',x=>stderr=(stderr+x).slice(-12000));const rpc=new RpcPeer(child.stdout,child.stdin);child.on('exit',code=>rpc.close(new Error('Server exited '+code+': '+stderr)));rpc.onRequest('workspace/configuration',p=>p.items.map(()=>null));rpc.onRequest('client/registerCapability',()=>null);
 return {child,rpc,stderr:()=>stderr};
}
async function main(){let local,reference;
 try{
  local=await server(process.execPath,[path.join(root,'vscode/src/lsp-server.cjs')]);reference=await server(dafny,['server','--cores','1','--cache-verification','0','--solver-path',z3]);
  const start=performance.now();
  await local.rpc.request('initialize',{rootUri:pathToFileURL(root).href,initializationOptions:{settings:{workers:1,automaticVerification:'never',timeoutMs:60000}}});
  await reference.rpc.request('initialize',{processId:process.pid,rootUri:pathToFileURL(directory).href,capabilities:{}});
  report.initializationMs=performance.now()-start;local.rpc.notify('initialized',{});reference.rpc.notify('initialized',{});
  let version=0;
  for(let round=0;round<3;round++)for(const [name,params,post,body,dparams,dpost,dbody] of cases){
   const method='run'+(++version),uri=pathToFileURL(path.join(directory,method+'.sol')).href,du=pathToFileURL(path.join(directory,method+'.dfy')).href,state=['assignment','increment'].includes(name),sol=`// SPDX-License-Identifier: MIT\npragma solidity ^0.8.34;\ncontract Simple { ${state?'uint value;':''}\n/// @custom:key ensures ${post}\nfunction ${method}(${params}) public ${state?'':'pure'} ${state?'':'returns (uint result)'} { ${body} }\n}\n`;
   const names=dparams?dparams.split(',').map(x=>x.trim().split(':')[0]):[],req=names.map(x=>`requires 0 <= ${x} < ${limit}`).join('\n');
   const dfy=`method ${method}(${dparams}) returns (r:int)\n${req}\n${name==='increment'?`requires value < ${max}`:''}\nensures 0 <= r < ${limit}\nensures ${dpost}\n{ ${dbody} }\n`;
   let statusResolve,statusReject,running=false,resolved=false,lastStatuses;
   // A new URI has no previous document result. Dafny may deliver the final
   // status before its resolution notification, so retain both events.
   const complete=()=>{if(resolved&&lastStatuses?.length&&lastStatuses.every(s=>[3,4,5].includes(s)))statusResolve(lastStatuses);};const statusTrace=[],compilationTrace=[];
   const status=new Promise((resolve,reject)=>{statusResolve=resolve;statusReject=reject;});
   const timer=setTimeout(()=>statusReject(new Error('Dafny status timeout: '+JSON.stringify({version,statusTrace,compilationTrace})+' '+reference.stderr())),60000);
   reference.rpc.onNotification('dafny/compilation/status',p=>{if(p.uri===du){compilationTrace.push(p);if(p.version===version&&p.status==='ResolutionSucceeded'){resolved=true;complete();}}});
   reference.rpc.onNotification('dafny/textDocument/symbolStatus',p=>{if(p.uri!==du||p.version!==version)return;const values=p.namedVerifiables.map(x=>x.status);statusTrace.push({resolved,values});lastStatuses=values;if(values.includes(2))running=true;complete();});
   const sd=performance.now();
   reference.rpc.notify('textDocument/didOpen',{textDocument:{uri:du,version,languageId:'dafny',text:dfy}});
   const statuses=await status.finally(()=>clearTimeout(timer)),dafnyMs=performance.now()-sd;
   assert.equal(resolved,true);assert.deepEqual(statuses,[name==='false-constant'?4:5]);
   const sl=performance.now();
   local.rpc.notify('textDocument/didOpen',{textDocument:{uri,version,languageId:'solidity',text:sol}});
   const result=await local.rpc.request('solidityLean/verify',{textDocument:{uri,version},options:{}},{timeoutMs:60000}),solidityMs=performance.now()-sl;
   assert.deepEqual(result.errors,[]);assert.deepEqual(result.results.map(x=>[x.function,x.status]),[[method,name==='false-constant'?'refuted':'proved']]);assert.equal(result.backend.kind,'generated-c-wasm');
   const sourceHash=createHash('sha256').update(sol).digest('hex');assert.ok(result.results.every(r=>r.sourceHash===sourceHash));
   const trial={name,round,version,solidityMs,dafnyMs,dafnyStatusTrace:statusTrace,sawRunning:running,soliditySource:sol,dafnySource:dfy,sourceHash,backend:result.backend,timings:result.timings};report.trials.push(trial);console.log(JSON.stringify({name,round,solidityMs,dafnyMs}));
   reference.rpc.notify('textDocument/didClose',{textDocument:{uri:du}});local.rpc.notify('textDocument/didClose',{textDocument:{uri}});
  }
  assert.equal(new Set(report.trials.map(t=>t.backend.workerPid)).size,1);report.passed=true;
 }finally{
  for(const s of [local,reference])if(s){try{await s.rpc.request('shutdown',null,{timeoutMs:2000});s.rpc.notify('exit');}catch{}s.child.kill();}
  fs.writeFileSync(process.argv[2]||path.join(root,'.lake/compiled-dafny-speed.json'),JSON.stringify(report,null,2)+'\n');fs.rmSync(directory,{recursive:true,force:true});
 }
}
main().catch(e=>{console.error(e);process.exitCode=1;});
