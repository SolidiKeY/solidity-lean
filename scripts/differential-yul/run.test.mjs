import test from 'node:test';
import assert from 'node:assert/strict';
import {mkdtempSync, symlinkSync, rmSync} from 'node:fs';
import {tmpdir} from 'node:os';
import {join} from 'node:path';
import {argumentsFor, run} from './run.mjs';
const base=['--compiler',process.execPath,'--driver',process.execPath,'--output','/tmp/new-yul-run'];
test('runner defaults to 2000, rejects ambiguous and invalid CLI options',()=>{
  assert.equal(argumentsFor(base).count,2000);
  for(const extra of [['--count','0'],['--count','10001'],['--seed','4294967296'],['--timeout','0'],['--fuel','1.5'],['--unknown','1'],['--count','2','--count','3']])
    assert.throws(()=>argumentsFor([...base,...extra]));
  assert.throws(()=>argumentsFor([]));
});
test('blocked orchestration cannot yield a successful CLI status',async()=>{
  let appends=0,finished=false,aborted=false;
  const config=argumentsFor([...base,'--count','2']);
  const {exitCode}=await run(config,{
    loadCompiler:async()=>()=>{},transport:()=>()=>{},
    openRun:()=>({append:()=>appends++,finish:()=>{finished=true;return{}},abort:()=>{aborted=true}}),
    runCase:async(record)=>({index:record.index,sourceSha256:(await import('node:crypto')).createHash('sha256').update(record.source).digest('hex'),optimizer:true,
      results:['ir','irOptimized'].map(stage=>({stage,status:'blocked',phase:'lean',reason:'test refusal'}))})
  });
  assert.equal(exitCode,2);assert.equal(appends,2);assert.ok(finished&&aborted);
});

test('execution and fingerprints use the same resolved driver path',async()=>{
  const dir=mkdtempSync(join(tmpdir(),'yul-run-test-'));
  const alias=join(dir,'driver'); symlinkSync(process.execPath,alias);
  const config=argumentsFor(['--compiler',alias,'--driver',alias,'--output',join(dir,'out'),'--count','1']);
  let driver,inputs;
  try {
    await assert.rejects(run(config,{
      loadCompiler:async path=>{assert.equal(path,process.execPath);return()=>{}},
      transport:options=>{driver=options.executable;return()=>{}},
      openRun:(_path,options)=>{inputs=options.inputPaths;throw Error('stop before execution')}
    }),/stop before execution/);
    assert.equal(driver,process.execPath);assert.ok(inputs.includes(driver));assert.ok(!inputs.includes(alias));
  } finally {rmSync(dir,{recursive:true,force:true})}
});

for (const mode of ['agree','mismatch','mixed']) test('runner status and stage findings: '+mode,async()=>{
  const findings=[];
  const config=argumentsFor([...base,'--count','1']);
  const result=await run(config,{
    loadCompiler:async()=>()=>{},transport:()=>()=>{},
    openRun:()=>({append:()=>{},writeFinding:value=>findings.push(value),finish:()=>({}),abort:()=>{}}),
    runCase:async(record)=>{
      const reference={failed:false,returnData:'0x',exception:null,slots:['0','1'],storage:['0','0']};
      return {index:record.index,sourceSha256:(await import('node:crypto')).createHash('sha256').update(record.source).digest('hex'),optimizer:true,reference,
        results:['ir','irOptimized'].map(stage=>mode==='mixed'&&stage==='irOptimized'
          ?{stage,status:'blocked',phase:'lean',reason:'test refusal'}
          :{stage,status:mode==='agree'?'agree':'mismatch',lean:{...reference,returnData:mode==='agree'?'0x':'0x01'}})};
    }
  });
  assert.equal(result.exitCode,{agree:0,mismatch:1,mixed:2}[mode]);
  assert.deepEqual(findings.map(x=>x.stage),mode==='agree'?[]:mode==='mixed'?['ir']:['ir','irOptimized']);
  for(const finding of findings) {assert.equal(finding.fields,'returnData');assert.match(finding.triage,/untriaged/);assert.equal(typeof finding.complete,'boolean');}
});
