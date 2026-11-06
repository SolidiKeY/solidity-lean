'use strict';
// Real extension LSP, including source compilation, transport and freshness
// checks. A new URI per submission prevents report-cache retrieval.
const fs=require('node:fs'),path=require('node:path'),assert=require('node:assert/strict');
const {spawn}=require('node:child_process');
const {pathToFileURL}=require('node:url');
const {RpcPeer}=require('../src/rpc.cjs');
const root=path.resolve(__dirname,'../..'),directory=path.join(root,'.lake/testsuite-performance');
const inputs=JSON.parse(fs.readFileSync(path.join(directory,'inputs.json'),'utf8'));
const repeats=Number(process.env.TESTSUITE_REPEATS||3);
async function main(){
 const {validateInputs}=await import('../../scripts/testsuite-performance.mjs');validateInputs(inputs);
 const started=performance.now(),child=spawn(process.execPath,[path.join(root,'vscode/src/lsp-server.cjs')],{cwd:root,stdio:['pipe','pipe','pipe']});
 let stderr='';child.stderr.on('data',d=>stderr=(stderr+d).slice(-8000));
 const rpc=new RpcPeer(child.stdout,child.stdin);child.on('exit',code=>rpc.close(new Error('LSP exited '+code+': '+stderr)));
 rpc.onRequest('workspace/configuration',p=>p.items.map(()=>null));rpc.onRequest('client/registerCapability',()=>null);
 const report={startedAt:new Date().toISOString(),inventorySha256:inputs.inventorySha256,trials:[]};
 try{
  await rpc.request('initialize',{rootUri:pathToFileURL(root).href,initializationOptions:{settings:{workers:1,automaticVerification:'never',timeoutMs:60000}}});
  rpc.notify('initialized',{});report.initializationMs=performance.now()-started;
  for(let round=0;round<repeats;round++)for(const input of inputs.trials){
   const uri=pathToFileURL(path.join(directory,input.name+'-'+round+'.sol')).href;
   const text=fs.readFileSync(input.source,'utf8'),start=performance.now();
   rpc.notify('textDocument/didOpen',{textDocument:{uri,version:1,languageId:'solidity',text}});
   const result=await rpc.request('solidityLean/verify',{textDocument:{uri,version:1},options:{}},{timeoutMs:60000});
   assert.deepEqual(result.errors,[]);assert.equal(result.results.length,1);
   assert.equal(result.results[0].status,'proved',input.name);assert.equal(result.results[0].function,input.name);assert.equal(result.results[0].sourceHash,input.sourceHash);
   assert.ok(['generated-c-native','generated-c-wasm'].includes(result.backend.kind));
   assert.ok(result.backend.directChecks.every(c=>c.environmentImports===0));
   report.trials.push({name:input.name,round,sourceHash:input.sourceHash,wallMs:performance.now()-start,...result});
   rpc.notify('textDocument/didClose',{textDocument:{uri}});
  }
  assert.equal(new Set(report.trials.map(t=>t.backend.workerPid)).size,1);
  assert.deepEqual(report.trials.map(t=>t.backend.directChecks[0].checkSequence),report.trials.map((_,i)=>i+1));
  report.passed=true;
 }finally{
  try{await rpc.request('shutdown',null,{timeoutMs:2000});rpc.notify('exit');}catch{}
  child.kill();
  fs.writeFileSync(process.env.TESTSUITE_EXTENSION_REPORT||path.join(directory,'extension.json'),JSON.stringify(report,null,2)+'\n');
 }
 console.log(JSON.stringify({passed:report.passed,initializationMs:report.initializationMs,trials:report.trials.length}));
}
main().catch(error=>{console.error(error);process.exitCode=1;});
