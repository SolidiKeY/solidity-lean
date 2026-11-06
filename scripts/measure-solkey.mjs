#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import {spawn,spawnSync} from 'node:child_process';
import {setTimeout as delay} from 'node:timers/promises';
import assert from 'node:assert/strict';
import {createHash} from 'node:crypto';
const root=path.resolve(process.argv[2]),inputs=JSON.parse(fs.readFileSync(process.argv[3],'utf8'));
const output=path.resolve(process.argv[4]||'web/artifacts/simple-solkey-report.json');
fs.mkdirSync(path.dirname(output),{recursive:true});
const digest=bytes=>createHash('sha256').update(bytes).digest('hex');
const metadata=(command,args)=>{const r=spawnSync(command,args,{encoding:'utf8',cwd:root});assert.equal(r.status,0);return (r.stdout+r.stderr).trim();};
const patch=spawnSync('git',['diff','HEAD','--binary'],{encoding:'utf8',cwd:root});assert.equal(patch.status,0);
const spool=fs.mkdtempSync('/tmp/solkey-measurement-');
const env={...process.env,SOLKEY_SPOOL:spool,...(process.env.SOLKEY_JAVA_HOME?{SOLKEY_JAVA_HOME:process.env.SOLKEY_JAVA_HOME}:{}),JAVA_TOOL_OPTIONS:`${process.env.JAVA_TOOL_OPTIONS||''} -Xmx2g -XX:ActiveProcessorCount=2 -Duser.home=${path.resolve('.lake/solkey-java-home')}`};
const report={startedAt:new Date().toISOString(),commit:metadata('git',['rev-parse','HEAD']),patchSha256:digest(patch.stdout),jarSha256:digest(fs.readFileSync(path.join(root,'keyext.solidity.core/build/libs/keyext.solidity.core-exe.jar'))),javaVersion:metadata(env.SOLKEY_JAVA_HOME?path.join(env.SOLKEY_JAVA_HOME,'bin/java'):metadata(path.join(root,'run-key.sh'),['--java-path']),['-version']),trials:[]};
let server;
function trial(input,mode){
  assert.equal(digest(fs.readFileSync(input.source)),input.sourceHash,'SolKey must read the exact matched source bytes');
  const start=performance.now();
  const functionName=input.function||'run';
  const run=spawnSync(path.join(root,'run-key.sh'),[input.source,'--contract',input.contract||'Simple','--function',functionName,'--json'],{cwd:root,env:{...env,SOLKEY_SERVER:mode==='cold'?'0':'1'},encoding:'utf8',timeout:300000,maxBuffer:16*1024**2});
  if(run.error)throw run.error;
  assert.equal(digest(fs.readFileSync(path.join(root,'keyext.solidity.core/build/libs/keyext.solidity.core-exe.jar'))),report.jarSha256,'benchmark JAR changed during execution; build it first');
  assert.equal(digest(fs.readFileSync(input.source)),input.sourceHash,'benchmark source changed during execution');
  const results=run.stdout.split('\n').filter(line=>line.startsWith('{')).map(line=>JSON.parse(line)).filter(row=>row.function);
  assert.deepEqual(results.map(row=>row.function),[functionName],run.stdout+'\n'+run.stderr);
  if(input.status!==undefined){
    assert.deepEqual(results.map(row=>row.status),[input.status==='proved'?'PROVED':'OPEN'],run.stdout+'\n'+run.stderr);
    assert.equal(run.status,input.status==='proved'?0:1,run.stderr);
  }else assert.ok(run.status===0||run.status===1,run.stdout+'\n'+run.stderr);
  const result={name:input.name,repeat:input.repeat,sourceHash:input.sourceHash,mode,wallMs:performance.now()-start,results};
  report.trials.push(result);console.log(JSON.stringify(result));
}
try{
  trial(inputs.trials[0],'cold');
  const start=performance.now();
  server=spawn(path.join(root,'run-key.sh'),['--serve'],{cwd:root,env,stdio:['ignore','pipe','pipe']});
  let logs='';server.stdout.on('data',data=>{logs+=data;});server.stderr.on('data',data=>{logs+=data;});
  while(!fs.existsSync(path.join(spool,'alive'))){assert.equal(server.exitCode,null,logs);if(performance.now()-start>30000)throw new Error('Server startup timeout: '+logs);await delay(50);}
  report.serverStartupMs=performance.now()-start;
  for(const input of inputs.trials)trial(input,'server');
  report.passed=true;
}finally{
  if(server){spawnSync(path.join(root,'run-key.sh'),['--stop-server'],{cwd:root,env,timeout:10000});if(server.exitCode===null){server.kill('SIGTERM');await Promise.race([new Promise(resolve=>server.once('exit',resolve)),delay(10000)]);if(server.exitCode===null)server.kill('SIGKILL');}}
  fs.rmSync(spool,{recursive:true,force:true});fs.writeFileSync(output,JSON.stringify(report,null,2)+'\n');
}
