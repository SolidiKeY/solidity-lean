'use strict';
const {test}=require('node:test');
const assert=require('node:assert/strict');
const {mkdtempSync,writeFileSync,readFileSync,rmSync,mkdirSync}=require('node:fs');
const {tmpdir}=require('node:os');
const {join,resolve}=require('node:path');
const {LspFrames,statistics,normalize,differences,summarize,ProcessSampler}=require('../parity/core.cjs');
const {validate,scan}=require('../parity/discover.cjs');
const {parse,launch}=require('../parity/run.cjs');
const {workload}=require('../parity/workloads.cjs');
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
  for(const args of [['--trials','0'],['--workers','0'],['--workers','1,1'],['--cache','pretend'],['--targets','fake'],['--targets','local,local'],['--obligations','1001'],['--unknown','x'],['--code']]) assert.throws(()=>parse(args));
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
