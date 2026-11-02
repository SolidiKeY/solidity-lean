#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import {spawnSync} from 'node:child_process';
import assert from 'node:assert/strict';
import {createHash} from 'node:crypto';
import {lakeCommand} from './lake-command.mjs';
const directory=path.resolve(process.argv[2]||'.lake/simple-measurement');
const output=path.resolve(process.argv[3]||'web/artifacts/simple-native-report.json');
fs.mkdirSync(path.dirname(output),{recursive:true});
const digest=bytes=>createHash('sha256').update(bytes).digest('hex');
const inputs=JSON.parse(fs.readFileSync(path.join(directory,'inputs.json'),'utf8'));
for(const input of inputs.trials){assert.equal(digest(fs.readFileSync(input.source)),input.sourceHash);fs.rmSync(input.output,{force:true});}
const frontend=path.resolve(process.env.BENCH_FRONTEND||'.lake/build/lib/lean/Solidity/Frontend/Testing.olean');
if(process.env.BENCH_LEAN)assert.ok(process.env.BENCH_FRONTEND,'BENCH_LEAN requires BENCH_FRONTEND pointing at the artifact loaded through LEAN_PATH');
const command=process.env.BENCH_LEAN||lakeCommand(process.env,process.cwd());
const arguments_=process.env.BENCH_LEAN?[path.join(directory,'Native.lean'),'-j1','--tstack=131072','-DElab.async=false']:['--quiet','--no-build','lean',path.join(directory,'Native.lean'),'--','-j1','--tstack=131072','-DElab.async=false'];
if(process.env.BENCH_PLUGIN)arguments_.push('--plugin='+path.resolve(process.env.BENCH_PLUGIN));
const pluginBuild=process.env.BENCH_PLUGIN?JSON.parse(fs.readFileSync(path.join(path.dirname(path.resolve(process.env.BENCH_PLUGIN)),'build.json'),'utf8')):null;
const startedAt=new Date().toISOString();
const start=performance.now();
const run=spawnSync(process.execPath,['scripts/tool-job.mjs',path.join(directory,'native-status.json'),'300000',
  command,...arguments_],
  {encoding:'utf8',timeout:315000,maxBuffer:32*1024**2});
const report={startedAt,frontendPath:frontend,frontendSha256:digest(fs.readFileSync(frontend)),pluginSha256:process.env.BENCH_PLUGIN?digest(fs.readFileSync(process.env.BENCH_PLUGIN)):null,pluginOptimization:pluginBuild?.optimization,wallMs:performance.now()-start,status:run.status,phases:[],trials:[]};
fs.writeFileSync(output+'.log',run.stdout+'\n'+run.stderr);
try{
  if(run.error)throw run.error;
  assert.equal(run.status,0,(run.stdout+'\n'+run.stderr).slice(-5000));
  report.nativeProbeCount=((run.stdout+'\n'+run.stderr).match(/NATIVE_FRONTEND_PROBE/g)||[]).length;
  if(pluginBuild?.nativeProbe)assert.equal(report.nativeProbeCount,inputs.trials.length,'every measured command must execute compiled C');
  report.phases=(run.stdout+'\n'+run.stderr).split('\n').filter(line=>line.startsWith('SOLKEY_BENCH ')).map(line=>JSON.parse(line.slice(13)));
  for(const input of inputs.trials){
    const results=JSON.parse(fs.readFileSync(input.output,'utf8'));
    assert.deepEqual(results.map(row=>[row.function,row.status]),[['run',input.status]]);
    const prefix=`${input.name}-${input.repeat}:`;
    const phases=report.phases.filter(phase=>phase.phase.startsWith(prefix));
    assert.equal(phases.length,3,'all frontend commands must be timed');
    report.trials.push({...input,results,phases,checkMs:phases.reduce((sum,phase)=>sum+phase.nanos/1e6,0)});
  }
  report.passed=true;console.log(JSON.stringify({wallMs:report.wallMs,trials:report.trials.map(t=>({name:t.name,repeat:t.repeat,checkMs:t.checkMs})),passed:true}));
}finally{fs.writeFileSync(output,JSON.stringify(report,null,2)+'\n');}
