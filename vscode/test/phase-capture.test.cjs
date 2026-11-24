// Protocol fixtures for phase coordination; fake image bytes are never parity evidence.
'use strict';
const test=require('node:test'),assert=require('node:assert/strict'),fs=require('node:fs'),path=require('node:path'),os=require('node:os');
const {paths,requestPhase,servePhases}=require('../parity/phase-capture.cjs');
const png=Buffer.from('iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAYAAAAfFcSJAAAADUlEQVR4nGNgYGD4DwABBAEAX+XDSwAAAABJRU5ErkJggg==','base64');
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

test('native capture acknowledgement cannot retain success alongside an internal error',async()=>{
 const dir=fixture();try{const pending=requestPhase(dir,'ack-error','trace-hidden',{binding:'owned'},1000);await servePhases(dir,'ack-error',async d=>{fs.writeFileSync(path.join(d,'screenshot.png'),png);return{captured:true,screenshot:true};},new Set());const reply=await pending;assert.equal(reply.error,undefined,'internal error cannot accompany accepted capture');}finally{fs.rmSync(dir,{recursive:true,force:true});}
});

test('captured status with an error and mismatched source metadata never satisfy the caller',async()=>{
 for(const wrongHash of [false,true]){const dir=fixture();try{const pending=requestPhase(dir,'poison','trace-hidden',{binding:'current'},1000),p=paths(dir,'trace-hidden'),request=JSON.parse(fs.readFileSync(p.request));const rejected=assert.rejects(pending,/mismatch|failed/);fs.writeFileSync(path.join(p.dir,'screenshot.png'),png);fs.writeFileSync(p.reply,JSON.stringify({runId:request.runId,phase:request.phase,requestId:request.requestId,status:'captured',error:'internal error',metadataHash:wrongHash?'wrong':require('node:crypto').createHash('sha256').update(JSON.stringify(request.metadata)).digest('hex')}));await rejected;}finally{fs.rmSync(dir,{recursive:true,force:true});}}
});

test('proof hover phase is explicitly allowlisted without permitting arbitrary phase paths',()=>{assert.match(paths('/tmp/root','proof-help-hover').dir,/proof-help-hover$/);assert.throws(()=>paths('/tmp/root','proof-help-hover/../../escape'),/Unknown/);});


test('reply and PNG reads cannot accept success at or beyond the phase deadline',async t=>{
  const originalRead=fs.readFileSync;
  for(const delayedFile of ['reply.json','screenshot.png']) for(const elapsed of [999,1000,1001]){
    const dir=fixture();let now=0,producerDone=false;
    try{
      t.mock.method(Date,'now',()=>now);
      t.mock.method(fs,'readFileSync',(file,...args)=>{
        const bytes=originalRead(file,...args);
        if(producerDone&&path.basename(String(file))===delayedFile)now=elapsed;
        return bytes;
      });
      const pending=requestPhase(dir,'read-budget','verified',{version:3},1000);
      const checked=elapsed<1000?pending:assert.rejects(pending,e=>e.code==='TIMEOUT');
      await servePhases(dir,'read-budget',async d=>{
        fs.writeFileSync(path.join(d,'screenshot.png'),png);
        return{captured:true,screenshot:true};
      },new Set());
      producerDone=true;await checked;
    }finally{t.mock.restoreAll();fs.rmSync(dir,{recursive:true,force:true});}
  }
});

test('request persistence consumes the existing phase budget',async t=>{
  const originalWrite=fs.writeFileSync;
  for(const elapsed of [999,1000,1001]){
    const dir=fixture();let now=0;
    try{
      t.mock.method(Date,'now',()=>now);
      t.mock.method(fs,'writeFileSync',(file,...args)=>{
        const value=originalWrite(file,...args);
        if(path.basename(String(file)).startsWith('request-attempt-')&&path.basename(String(file)).endsWith('.json.tmp'))now=elapsed;
        return value;
      });
      const pending=requestPhase(dir,'write-budget','open',{},1000);
      const checked=elapsed<1000?pending:assert.rejects(pending,e=>e.code==='TIMEOUT');
      await servePhases(dir,'write-budget',async d=>{
        fs.writeFileSync(path.join(d,'screenshot.png'),png);
        return{captured:true,screenshot:true};
      },new Set());
      await checked;
    }finally{t.mock.restoreAll();fs.rmSync(dir,{recursive:true,force:true});}
  }
});


test('late reads retain renderer and invalid-PNG failures',async t=>{
  const originalRead=fs.readFileSync;
  for(const failure of ['renderer','png']){
    const dir=fixture();let now=0,producerDone=false;
    try{
      t.mock.method(Date,'now',()=>now);
      t.mock.method(fs,'readFileSync',(file,...args)=>{
        const bytes=originalRead(file,...args);
        if(producerDone&&path.basename(String(file))===(failure==='renderer'?'reply.json':'screenshot.png'))now=1000;
        return bytes;
      });
      const pending=requestPhase(dir,'read-failure','verified',{},1000);
      const rejected=assert.rejects(pending,failure==='renderer'?/CDP disconnected/:/no PNG evidence/);
      await servePhases(dir,'read-failure',async d=>{
        if(failure==='renderer')throw Error('CDP disconnected');
        fs.writeFileSync(path.join(d,'screenshot.png'),Buffer.from('invalid'));
        return{captured:true,screenshot:true};
      },new Set());
      producerDone=true;await rejected;
    }finally{t.mock.restoreAll();fs.rmSync(dir,{recursive:true,force:true});}
  }
});

test('renderer acknowledgement refuses truthy nonbooleans and nested capture errors',async()=>{
 for(const capture of [{captured:'false',screenshot:true},{captured:true,screenshot:'false'},{captured:1,screenshot:true},{captured:true,screenshot:1},{captured:true,screenshot:true,error:'actual renderer failure'}]){
  const dir=fixture();try{
   const pending=requestPhase(dir,'strict-capture','trace-hidden',{binding:'owned'},1000),rejected=assert.rejects(pending,/failed/);
   await servePhases(dir,'strict-capture',async d=>{fs.writeFileSync(path.join(d,'screenshot.png'),png);return capture;},new Set());
   await rejected;const reply=JSON.parse(fs.readFileSync(paths(dir,'trace-hidden').reply));assert.equal(reply.status,'failed');assert.deepEqual(reply.capture,capture);if(capture.error)assert.equal(reply.error,capture.error);
  }finally{fs.rmSync(dir,{recursive:true,force:true});}
 }
});

test('preexisting phase image refuses renderer input and remains unchanged',async()=>{
 const dir=fixture();try{
  const p=paths(dir,'trace-hidden');fs.mkdirSync(p.dir,{recursive:true});const old=Buffer.concat([png,Buffer.from('old retained image')]);fs.writeFileSync(path.join(p.dir,'screenshot.png'),old);
  const pending=requestPhase(dir,'fresh-request','trace-hidden',{binding:'new-source'},1000),rejected=assert.rejects(pending,/failed/);let captures=0;
  await servePhases(dir,'fresh-request',async()=>{captures++;return{captured:true,screenshot:true};},new Set());await rejected;
  assert.equal(captures,0);assert.deepEqual(fs.readFileSync(path.join(p.dir,'screenshot.png')),old);const reply=JSON.parse(fs.readFileSync(p.reply));assert.equal(reply.status,'failed');assert.match(reply.error,/Existing phase screenshot/);
 }finally{fs.rmSync(dir,{recursive:true,force:true});}
});

test('acknowledged image bytes cannot be substituted before the client reads them',async()=>{
 for(const sameLength of [false,true]){const dir=fixture();try{
  const pending=requestPhase(dir,'image-binding','trace-hidden',{source:'owned'},1000),rejected=assert.rejects(pending,/image.*mismatch/i);
  await servePhases(dir,'image-binding',async d=>{fs.writeFileSync(path.join(d,'screenshot.png'),png);return{captured:true,screenshot:true};},new Set());
  const p=paths(dir,'trace-hidden'),substitution=Buffer.from(sameLength?'iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAYAAAAfFcSJAAAADUlEQVR4nGNgZGD4DwABCAEBfBRbtQAAAABJRU5ErkJggg==':'iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAYAAAAfFcSJAAAADUlEQVR4nGNgYGD4DwABBAEAX+XDSwAAAA50RVh0bm90ZQBhbHRlcm5hdGW4ZEnDAAAAAElFTkSuQmCC','base64');assert.equal(substitution.length===png.length,sameLength);
  fs.writeFileSync(path.join(p.dir,'screenshot.png'),substitution);await rejected;
 }finally{fs.rmSync(dir,{recursive:true,force:true});}}
});

test('producer image binding remains inside the original client phase budget',async t=>{
 const dir=fixture(),read=fs.readFileSync;let clock=0;try{
  t.mock.method(Date,'now',()=>clock);t.mock.method(fs,'readFileSync',(file,...args)=>{const bytes=read(file,...args);if(path.basename(String(file))==='screenshot.png')clock=1000;return bytes;});
  const pending=requestPhase(dir,'producer-budget','trace-hidden',{},1000),rejected=assert.rejects(pending,e=>e.code==='TIMEOUT');
  await servePhases(dir,'producer-budget',async d=>{fs.writeFileSync(path.join(d,'screenshot.png'),png);return{captured:true,screenshot:true};},new Set());await rejected;
 }finally{t.mock.restoreAll();fs.rmSync(dir,{recursive:true,force:true});}
});

test('a second phase request cannot overwrite an active or completed request',async()=>{
 const dir=fixture();try{
  const first=requestPhase(dir,'phase-slot','trace-hidden',{source:'first'},1000),p=paths(dir,'trace-hidden'),original=fs.readFileSync(p.request);
  const firstFailure=first.catch(()=>{});
  await assert.rejects(requestPhase(dir,'phase-slot','trace-hidden',{source:'second'},1000),e=>e.code==='EEXIST');assert.deepEqual(fs.readFileSync(p.request),original);
  await servePhases(dir,'phase-slot',async d=>{fs.writeFileSync(path.join(d,'screenshot.png'),png);return{captured:true,screenshot:true};},new Set());await first;
  await assert.rejects(requestPhase(dir,'phase-slot','trace-hidden',{source:'third'},1000),e=>e.code==='EEXIST');assert.deepEqual(fs.readFileSync(p.request),original);
  const attempts=fs.readdirSync(p.dir).filter(n=>n.startsWith('request-attempt-')&&n.endsWith('.json')).map(n=>JSON.parse(fs.readFileSync(path.join(p.dir,n))));assert.deepEqual(attempts.map(a=>a.metadata.source).sort(),['first','second','third']);await firstFailure;
 }finally{fs.rmSync(dir,{recursive:true,force:true});}
});
