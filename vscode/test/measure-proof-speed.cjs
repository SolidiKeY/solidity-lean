'use strict';
const fs=require('node:fs'),path=require('node:path'),assert=require('node:assert/strict');
const {fork}=require('node:child_process');
const {createHash}=require('node:crypto');
const root=path.resolve(__dirname,'../..'),inputs=JSON.parse(fs.readFileSync(path.join(root,'.lake/simple-measurement/inputs.json')));
const imports=fs.readFileSync(path.join(root,'.lake/simple-measurement/Native.lean'),'utf8').split('\n');
const output=path.resolve(process.argv[2]||path.join(root,'vscode/parity/artifacts/proof-speed.json'));
async function main(){
 const directory=fs.mkdtempSync(path.join(root,'.lake/extension-speed-'));
 const child=fork(path.join(root,'vscode/src/lsp-worker.cjs'),[],{cwd:root,stdio:['ignore','pipe','pipe','ipc']});
 let stderr='';child.stderr.on('data',x=>stderr=(stderr+x).slice(-12000));
 const closedSpecs=process.env.PROOF_SPEED_CLOSED_SPECS!=='0';
 const report={startedAt:new Date().toISOString(),closedSpecs,trials:[]};let id=0;
 try{
  for(const input of inputs.trials){
   const text=fs.readFileSync(input.source,'utf8'),fixtureText=fs.readFileSync(input.fixture,'utf8'),fixture=JSON.parse(fixtureText);
   assert.equal(createHash('sha256').update(text).digest('hex'),input.sourceHash);
   const hash=imports.find(x=>x.includes('solc_import '+JSON.stringify(input.fixture)+' ')).match(/ hash (0x[0-9a-f]+) /)[1];
   const start=performance.now(),taskId=++id;
   const result=await new Promise((resolve,reject)=>{
    const timer=setTimeout(()=>{cleanup();reject(new Error('Proof timeout: '+stderr));},90000);
    const onExit=()=>{cleanup();reject(new Error('Worker exited: '+stderr));};
    const onMessage=m=>{if(m.id!==taskId)return;cleanup();if(m.error)reject(new Error(JSON.stringify(m.error)));else resolve(m.result);};
    const cleanup=()=>{clearTimeout(timer);child.off('message',onMessage);child.off('exit',onExit);};
    child.on('message',onMessage);child.on('exit',onExit);
    child.send({id:taskId,action:'verify',root,directory,source:path.join(directory,'Simple.sol'),text,
      compiled:{text:fixtureText,fixture,hash,sourceHash:input.sourceHash},options:{timeoutMs:90000,closedSpecs}});
   });
   assert.deepEqual(result.errors,[]);assert.deepEqual(result.results.map(x=>[x.function,x.status]),[['run',input.status]]);
   assert.ok(result.results.every(x=>x.sourceHash===input.sourceHash));
   const trial={name:input.name,repeat:input.repeat,sourceHash:input.sourceHash,elapsedMs:performance.now()-start,...result};
   report.trials.push(trial);console.log(JSON.stringify({name:trial.name,repeat:trial.repeat,elapsedMs:trial.elapsedMs,backend:trial.backend}));
  }
  assert.equal(new Set(report.trials.map(t=>t.backend.leanServerPid)).size,1);
  assert.deepEqual(report.trials.map(t=>t.backend.leanDocumentVersion),Array.from({length:18},(_,i)=>i+1));
  report.passed=true;
 }finally{child.disconnect();await new Promise(resolve=>child.once('exit',resolve));fs.rmSync(directory,{recursive:true,force:true});fs.mkdirSync(path.dirname(output),{recursive:true});fs.writeFileSync(output,JSON.stringify(report,null,2)+'\n');}
}
main().catch(e=>{console.error(e);process.exitCode=1;});
