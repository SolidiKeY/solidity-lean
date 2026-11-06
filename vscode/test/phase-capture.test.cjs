// Protocol fixtures for phase coordination; fake image bytes are never parity evidence.
'use strict';
const test=require('node:test'),assert=require('node:assert/strict'),fs=require('node:fs'),path=require('node:path'),os=require('node:os');
const {paths,requestPhase,servePhases}=require('../parity/phase-capture.cjs');
const png=Buffer.from([137,80,78,71,13,10,26,10,0]);
const fixture=()=>fs.mkdtempSync(path.join(os.tmpdir(),'parity-phase-'));
test('fresh screenshot acknowledgements retain launch, phase and source snapshot identity',async()=>{
  const dir=fixture();try{
    const pending=requestPhase(dir,'launch-a','verified',{version:7,source:'current'},1000);
    await servePhases(dir,'launch-a',async d=>{fs.writeFileSync(path.join(d,'screenshot.png'),png);return{captured:true,screenshot:true};},new Set());
    const reply=await pending;assert.equal(reply.phase,'verified');assert.equal(reply.runId,'launch-a');
    assert.equal(JSON.parse(fs.readFileSync(paths(dir,'verified').request)).metadata.version,7);
  }finally{fs.rmSync(dir,{recursive:true,force:true});}
});
test('acknowledgements from other launches cannot satisfy or overwrite the current capture',async()=>{
  const dir=fixture();try{
    const p=paths(dir,'open');fs.mkdirSync(p.dir,{recursive:true});fs.writeFileSync(p.reply,JSON.stringify({runId:'old-launch',phase:'open',status:'captured'}));
    const pending=requestPhase(dir,'current-launch','open',{},100);
    let captures=0;await servePhases(dir,'wrong-launch',async()=>{captures++;},new Set());
    await assert.rejects(pending,/Timed out/);assert.equal(captures,0);
  }finally{fs.rmSync(dir,{recursive:true,force:true});}
});
test('renderer success without a screenshot and renderer failures remain failing evidence',async()=>{
  for(const capture of [async()=>({captured:true,screenshot:false}),async()=>{throw Error('CDP disconnected');},async()=>({captured:true,screenshot:true})]){
    const dir=fixture();try{
      const pending=requestPhase(dir,'run','proof-broken',{},1000);
      // Attach the handler before serving, so an immediate failure is observed by the test runner.
      const rejected=assert.rejects(pending);
      await servePhases(dir,'run',capture,new Set());await rejected;
    }finally{fs.rmSync(dir,{recursive:true,force:true});}
  }
});
test('phase names cannot escape the artifact directory',()=>{assert.throws(()=>paths('/tmp/root','../../elsewhere'),/Unknown/);});

test('visual capture timings cannot be pooled into proof benchmark trials',()=>{
  const {summarize}=require('../parity/core.cjs');
  const groups=summarize([{target:'local',workers:1,cache:'none',suite:'full',status:'passed',result:{metrics:{activationMs:100}}},{target:'local',workers:1,cache:'none',suite:'visual',status:'passed-with-gaps',result:{metrics:{activationMs:1}}}]);
  assert.equal(groups.length,2);assert.equal(groups.find(g=>g.suite==='full').metrics.activationMs.median,100);
});

test('finished proofs cannot be relabeled as open or first-feedback captures',()=>{
  const {phaseObserved}=require('../parity/phase-capture.cjs'),done={state:'complete',functions:[{status:'proved'}]},running={state:'running'};
  assert.equal(phaseObserved('open',undefined,done),false);assert.equal(phaseObserved('first-feedback',running,done),false);
  assert.equal(phaseObserved('first-feedback',running,running),true);assert.equal(phaseObserved('verified',done,done),true);
  assert.equal(phaseObserved('first-feedback',{namedVerifiables:[{status:5}]},{namedVerifiables:[{status:5}]}),false);
});

test('verified/fixed captures reject cancellation, errors, failed proofs and changed final symbol states',()=>{
  const {phaseObserved}=require('../parity/phase-capture.cjs'),proved={state:'complete',functions:[{status:'proved'}]},failed={state:'complete',functions:[{status:'pending'}]};
  for(const after of [{state:'cancelled'},{state:'error'},failed,{namedVerifiables:[{status:4}]}]){
    assert.equal(phaseObserved('verified',proved,after),false);assert.equal(phaseObserved('proof-fixed',proved,after),false);
  }
  assert.equal(phaseObserved('proof-broken',failed,failed),true);assert.equal(phaseObserved('proof-broken',proved,proved),false);
});
