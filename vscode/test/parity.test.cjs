'use strict';
const {test}=require('node:test');
const assert=require('node:assert/strict');
const {mkdtempSync,writeFileSync,readFileSync,rmSync,mkdirSync}=require('node:fs');
const {tmpdir}=require('node:os');
const {join,resolve}=require('node:path');
const {LspFrames,statistics,normalize,differences,summarize,scaling,protocol,hostEvidenceErrors,ProcessSampler}=require('../parity/core.cjs');
const {validate,scan}=require('../parity/discover.cjs');
const {parse,launch}=require('../parity/run.cjs');
const {workload,verificationOutcomes,servicesWorkload,assertServiceResponse}=require('../parity/workloads.cjs');
const {observe}=require('../parity/observe.cjs');
const {activity}=require('../parity/analyze.cjs');

test('LSP recorder reconstructs multibyte fragmented and coalesced messages',()=>{
  const messages=[{id:1,result:'é🦀'},{method:'textDocument/publishDiagnostics',params:{version:4,diagnostics:[]}}];
  const bytes=Buffer.concat(messages.map(message=>{const body=Buffer.from(JSON.stringify(message));return Buffer.concat([Buffer.from(`Content-Length: ${body.length}\r\n\r\n`),body]);}));
  for(const size of [1,2,7,bytes.length]){
    const frames=new LspFrames(),actual=[];frames.on('message',message=>actual.push(message));
    for(let i=0;i<bytes.length;i+=size)frames.push(bytes.subarray(i,i+size));
    frames.end();assert.deepEqual(actual,messages);
  }
});
test('LSP recorder refuses ambiguity, truncation and unbounded payloads',()=>{
  assert.throws(()=>new LspFrames().push(Buffer.from('Content-Length: 1\r\nContent-Length: 2\r\n\r\n{}')),/Invalid/);
  assert.throws(()=>new LspFrames(16).push(Buffer.from('Content-Length: 17\r\n\r\n')),/Oversize/);
  const frames=new LspFrames();frames.push(Buffer.from('Content-Length: 2\r\n\r\n{'));assert.throws(()=>frames.end(),/Truncated/);
});
test('normalization retains diagnostic severity, version, text, order and ranges',()=>{
  const value={uri:'file:///tmp/run/a.sol',version:8,diagnostics:[{message:'assertion failed',severity:1,range:{start:{line:4,character:9}}}]};
  const canonical=normalize(value,['/tmp/run']);assert.equal(canonical.uri,'file://<workspace>/a.sol');
  assert.deepEqual(canonical.diagnostics,value.diagnostics);assert.equal(canonical.version,8);
  const changed={...canonical,version:9,diagnostics:[{...canonical.diagnostics[0],severity:2}]};
  assert.deepEqual(differences(canonical,changed).map(d=>d.path),['$.version','$.diagnostics.0.severity']);
});
test('statistics use median and nearest-rank p95; failed trials remain visible',()=>{
  assert.equal(statistics([9,1,4,2]).median,3);assert.equal(statistics([1,2,3,100]).p95,100);assert.equal(statistics([]).p95,null);
  const runs=[{target:'local',workers:1,cache:'none',status:'passed',result:{metrics:{hoverMs:4}}},
    {target:'local',workers:1,cache:'none',status:'timeout',result:{metrics:{}}},
    {target:'local',workers:1,cache:'none',warmup:true,status:'passed',result:{metrics:{hoverMs:100}}}];
  const [group]=summarize(runs);assert.equal(group.trials,2);assert.equal(group.timeoutRate,.5);assert.equal(group.failures,1);assert.equal(group.metrics.hoverMs.median,4);
});
test('failed launches cannot improve latency or manufacture parallel scaling',()=>{
  const runs=[{target:'local',workers:1,cache:'none',status:'passed',result:{metrics:{initialVerificationMs:1000}}},
    {target:'local',workers:1,cache:'none',status:'broken',result:{metrics:{initialVerificationMs:1}}},
    {target:'local',workers:2,cache:'none',status:'timeout',result:{metrics:{initialVerificationMs:1}}}];
  const groups=summarize(runs);
  assert.equal(groups[0].metrics.initialVerificationMs.median,1000);assert.equal(groups[0].validTrials,1);
  assert.equal(groups[0].excludedTimingTrials,1);assert.equal(groups[1].metrics.initialVerificationMs.n,0);
  assert.equal(scaling(groups)[1].speedup,null);assert.equal(groups[1].timeoutRate,1);
});
test('every verification scenario must check expected proof outcomes, not just terminal counts',()=>{
  const local=status=>({errors:[],results:[{function:'f0',status}]}),dafny=status=>({namedVerifiables:[{status}]});
  for(const status of ['pending','refuted','unsupported','error'])assert.throws(()=>verificationOutcomes('local',local(status),1),/Expected proved/);
  assert.throws(()=>verificationOutcomes('dafny',dafny(4),1),/Expected proved/);
  assert.throws(()=>verificationOutcomes('dafny',dafny(2),1),/Expected proved/);
  verificationOutcomes('local',local('proved'),1);verificationOutcomes('dafny',dafny(5),1);
  verificationOutcomes('local',local('refuted'),1,'failed');verificationOutcomes('dafny',dafny(4),1,'failed');
  assert.throws(()=>verificationOutcomes('local',local('pending'),1,'failed'),/Expected failed/);
  assert.throws(()=>verificationOutcomes('local',{errors:[],results:[{function:'f0',status:'proved'},{function:'f0',status:'proved'}]},2),/unique/);
  assert.throws(()=>verificationOutcomes('local',{errors:[],results:[{function:'f99',status:'proved'}]},1),/exact paired/);
});
test('service observations reject empty hover, wrong navigation and arbitrary rename edits',()=>{
  const fixture=servicesWorkload('dafny'),uri='file:///services.dfy';
  assert.throws(()=>assertServiceResponse('hover',fixture,uri,{contents:[]}),/nonempty/);
  assert.throws(()=>assertServiceResponse('hover',fixture,uri,{contents:{}}),/nonempty/);
  assert.throws(()=>assertServiceResponse('definition',fixture,uri,{uri,range:fixture.callRange}),/exact declaration/);
  assert.throws(()=>assertServiceResponse('rename',fixture,uri,{changes:{[uri]:[{range:fixture.callRange,newText:'wrong'},{range:fixture.declarationRange,newText:'wrong'}]}}),/replacement text/);
});
test('fresh report identity cannot conceal inconsistent or invented scenario passes',()=>{
  const config={runId:'fresh',target:'local'},base={schemaVersion:1,...config,status:'passed',scenarios:[{id:'initial-verification',status:'passed'}],checks:['initial-verification']};
  assert.deepEqual(hostEvidenceErrors(base,config),[]);
  for(const change of [{scenarios:[]},{scenarios:[{id:'initial-verification',status:'broken'}]},
    {scenarios:[...base.scenarios,...base.scenarios]},{checks:['initial-verification','invented']}])assert.ok(hostEvidenceErrors({...base,...change},config).length);
  const timedOut={...base,status:'timeout',checks:[],scenarios:[{id:'initial-verification',status:'timeout'}]};
  assert.deepEqual(hostEvidenceErrors(timedOut,config),[],'legitimate failure evidence must be retained');
});
test('empty, unfinalized and corrupt recordings cannot certify an observed protocol',()=>{
  const dir=mkdtempSync(join(tmpdir(),'parity-trace-')),file=join(dir,'lsp.jsonl');
  try{
    writeFileSync(file,'');assert.equal(protocol(file).status,'unexamined');
    const message={direction:'server',message:{jsonrpc:'2.0',method:'initialized',params:{}}};
    writeFileSync(file,JSON.stringify(message)+'\n');assert.equal(protocol(file).status,'partial');
    writeFileSync(file,[message,{direction:'server',framingFinalized:true},{direction:'client',framingFinalized:true}].map(r=>JSON.stringify(r)).join('\n'));
    assert.equal(protocol(file).status,'observed');
    require('node:fs').appendFileSync(file,'\n'+JSON.stringify({direction:'server',error:'Truncated LSP frame'}));
    assert.equal(protocol(file).status,'broken');
  }finally{rmSync(dir,{recursive:true,force:true});}
});
test('independent audit keeps all upstream registration sites explicitly unexamined',()=>{
  const {validate}=require('../parity/audit.cjs');
  const audit=JSON.parse(readFileSync(resolve(__dirname,'../../docs/dafny-editor-audit.json'),'utf8'));
  assert.deepEqual(validate(audit),[]);audit.testFiles[0].cases.push({id:'fake',status:'complete',runtimeEvidence:[]});
  assert.ok(validate(audit).length);
});
test('unsupported and untested capabilities cannot be marked complete',()=>{
  const inventory=JSON.parse(readFileSync(resolve(__dirname,'../../docs/dafny-editor-features.json'),'utf8'));
  assert.deepEqual(validate(inventory),[]);
  inventory.features[0].assessment.status='complete';assert.ok(validate(inventory).some(e=>e.includes('unsupported completeness')));
  inventory.features[0].assessment.testEvidence=[{status:'skipped',assertion:'something',artifact:'fake.json'}];
  assert.ok(validate(inventory).some(e=>e.includes('unsupported completeness')));
});
test('inventory shrinkage and invented upstream evidence fail the offline gate',()=>{
  const original=JSON.parse(readFileSync(resolve(__dirname,'../../docs/dafny-editor-features.json'),'utf8'));
  const fewer=structuredClone(original);fewer.features.pop();assert.ok(validate(fewer).some(e=>e.includes('feature set changed')));
  const tampered=structuredClone(original);tampered.features[0].upstream[0].sha256='0'.repeat(64);
  assert.ok(validate(tampered).some(e=>e.includes('unregistered upstream evidence')));
});
test('runner rejects ambiguous options and invalid benchmark dimensions',()=>{
  for(const args of [['--trials','0'],['--workers','0'],['--workers','5'],['--workers','1,1'],['--cache','pretend'],['--targets','fake'],['--targets','local,local'],['--obligations','1001'],['--unknown','x'],['--code']]) assert.throws(()=>parse(args));
  assert.deepEqual(parse(['--targets','dafny','--workers','8']).workers,[8]);
  assert.deepEqual(parse(['--workers','1,2,4']).workers,[1,2,4]);
  assert.throws(()=>workload('local',0));assert.match(workload('local',2,true),/@custom:key ensures \\result == 2/);
  assert.match(workload('dafny',2,true),/ensures r == 2/);
});
test('real process sampler observes its own process without claiming unsupported measurements',()=>{
  const sampler=new ProcessSampler(process.pid);const result=sampler.stop();
  if(process.platform==='linux'){assert.ok(result.peakRssBytes>0);assert.ok(result.samples.length>0);}
  assert.ok(result.limitations.length);
});
test('solver analysis distinguishes CPU work from sleeping solvers and the frontend',()=>{
  const process=(pid,name,ticks)=>({pid,name,ticks});
  const result=activity({platform:'linux',samples:[
    {processes:[process(1,'z3-4.12.1',3),process(2,'z3-4.12.1',8),process(3,'dafny',40)]},
    {processes:[process(1,'z3-4.12.1',4),process(2,'z3-4.12.1',8),process(3,'dafny',80)]},
    {processes:[process(1,'z3-4.12.1',4),process(2,'z3-4.12.1',9),process(3,'dafny',100)]}
  ]});
  assert.equal(result.peakLivingSolverProcesses,2);assert.equal(result.maxCpuActiveSolverProcesses,1);
  assert.equal(result.maxCpuActiveLeanProcesses,0);assert.equal(activity({platform:'win32'}).status,'unexamined');
});
test('child-process observation preserves custom promisify semantics and excludes unrelated extensions',async()=>{
  const dir=mkdtempSync(join(tmpdir(),'parity-observer-'));
  const vscode={tests:{},window:{},languages:{onDidChangeDiagnostics:()=>({dispose(){}})}};
  const observation=observe(vscode,()=>{},dir,null);
  try {
    const file=join(dir,'target.cjs');writeFileSync(file,'module.exports = require("node:child_process");\n');
    const wrapped=require(file),real=require('node:child_process');
    assert.equal(wrapped.execFile,real.execFile,'promisify.custom must remain attached');
    assert.notEqual(wrapped.spawn,real.spawn,'only the target spawn boundary is observed');
    const result=await require('node:util').promisify(wrapped.execFile)(process.execPath,['-e','process.stdout.write("runtime")']);
    assert.equal(result.stdout,'runtime');assert.equal(result.stderr,'');
  }finally{observation.restore();rmSync(dir,{recursive:true,force:true});}
});
for(const stale of [false,true])test(`offline parity launcher rejects ${stale?'stale success':'exit zero without fresh evidence'}`,async()=>{
  if(process.platform==='win32')return;
  const dir=mkdtempSync(join(tmpdir(),'parity-launcher-'));
  try {
    const code=join(dir,'code');writeFileSync(code,'#!/bin/sh\nexit 0\n',{mode:0o700});
    const trial=join(dir,'trial');mkdirSync(trial);
    const config={dir:trial,target:'local',workers:1,cache:'none',trial:0,warmup:false,workspace:join(trial,'workspace'),result:join(trial,'result.json'),events:join(trial,'events.jsonl'),trace:join(trial,'lsp.jsonl')};
    if(stale)writeFileSync(config.result,JSON.stringify({schemaVersion:1,runId:'old-launch',target:'local',status:'passed',scenarios:[{id:'initial-verification',status:'passed'}],checks:['initial-verification']}));
    const run=await launch(config,{code,operationTimeoutMs:1000,timeoutMs:2000,obligations:1});
    assert.equal(run.status,'broken');assert.match(run.error,stale?/stale/:/No fresh/);
  }finally{rmSync(dir,{recursive:true,force:true});}
});
test('a scenario timeout survives a successful editor exit in machine summaries',async()=>{
  if(process.platform==='win32')return;
  const dir=mkdtempSync(join(tmpdir(),'parity-timeout-'));
  try {
    const code=join(dir,'code');
    writeFileSync(code,`#!${process.execPath}\nconst fs=require('node:fs');const c=JSON.parse(fs.readFileSync(process.env.PARITY_HOST_CONFIG,'utf8'));fs.writeFileSync(c.result,JSON.stringify({schemaVersion:1,runId:c.runId,target:c.target,status:'timeout',checks:['initial-verification'],scenarios:[{id:'initial-verification',status:'passed'},{id:'rapid-edits-stale-results',status:'timeout'}]}));\n`,{mode:0o700});
    const trial=join(dir,'trial');
    const config={dir:trial,target:'local',workers:1,cache:'none',trial:0,warmup:false,workspace:join(trial,'workspace'),result:join(trial,'result.json'),events:join(trial,'events.jsonl'),trace:join(trial,'lsp.jsonl')};
    const run=await launch(config,{code,operationTimeoutMs:1000,timeoutMs:2000,obligations:1});
    assert.equal(run.status,'timeout');assert.equal(summarize([run])[0].timeoutRate,1);
  }finally{rmSync(dir,{recursive:true,force:true});}
});
test('a normal editor exit cannot leave a sampled detached verifier in the next trial',async()=>{
  if(process.platform!=='linux')return;
  const dir=mkdtempSync(join(tmpdir(),'parity-survivor-'));let pid;
  try {
    const code=join(dir,'code'),pidfile=join(dir,'pid');
    writeFileSync(code,`#!${process.execPath}\nconst fs=require('node:fs');const c=JSON.parse(fs.readFileSync(process.env.PARITY_HOST_CONFIG,'utf8'));const child=require('node:child_process').spawn(process.execPath,['-e','setInterval(()=>{},1000)'],{detached:true,stdio:'ignore'});child.unref();fs.writeFileSync(${JSON.stringify(pidfile)},String(child.pid));setTimeout(()=>fs.writeFileSync(c.result,JSON.stringify({schemaVersion:1,runId:c.runId,target:c.target,status:'passed',checks:['initial-verification'],scenarios:[{id:'initial-verification',status:'passed'}]})),350);\n`,{mode:0o700});
    const trial=join(dir,'trial');
    const config={dir:trial,target:'local',workers:1,cache:'none',trial:0,warmup:false,workspace:join(trial,'workspace'),result:join(trial,'result.json'),events:join(trial,'events.jsonl'),trace:join(trial,'lsp.jsonl')};
    const run=await launch(config,{code,operationTimeoutMs:1000,timeoutMs:3000,obligations:1});
    pid=Number(readFileSync(pidfile,'utf8'));
    assert.ok(run.resources.cleanup.terminatedOwnedSurvivors.some(p=>p.pid===pid));
    assert.deepEqual(run.resources.cleanup.remaining,[]);assert.equal(run.status,'passed');
  }finally{if(pid)try{process.kill(pid,'SIGKILL');}catch{}rmSync(dir,{recursive:true,force:true});}
});
test('long artifact paths do not become long editor IPC/profile paths',async()=>{
  if(process.platform==='win32')return;
  const dir=mkdtempSync(join(tmpdir(),'parity-path-'));
  try {
    const code=join(dir,'code'),record=join(dir,'launch.json');
    writeFileSync(code,`#!${process.execPath}\nrequire('node:fs').writeFileSync(${JSON.stringify(record)},JSON.stringify({portable:process.env.VSCODE_PORTABLE,args:process.argv}));\n`,{mode:0o700});
    const trial=join(dir,'long-artifacts-'.repeat(12));
    const config={dir:trial,target:'local',workers:1,cache:'none',trial:0,warmup:false,workspace:join(trial,'workspace'),result:join(trial,'result.json'),events:join(trial,'events.jsonl'),trace:join(trial,'lsp.jsonl')};
    await launch(config,{code,operationTimeoutMs:1000,timeoutMs:2000,obligations:1});
    const data=JSON.parse(readFileSync(record,'utf8'));
    assert.ok(join(data.portable,'user-data/1.10-main.sock').length<107);
    assert.equal(data.portable.startsWith(trial),false);
    assert.equal(require('node:fs').existsSync(data.portable),false,'temporary editor state is removed');
  }finally{rmSync(dir,{recursive:true,force:true});}
});
