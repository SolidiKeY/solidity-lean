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
// Injected editors exercise the launcher, not the host: they launch under an
// admitted snapshot. resourcesAllowed is tested in proof-help.test.cjs; the
// launcher's refusal under an injected swap snapshot is tested below.
const admitted=()=>({availableBytes:16*1024**3,swapTotalBytes:0});

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
  const {validate,validateIndex}=require('../parity/audit.cjs');
  const audit=JSON.parse(readFileSync(resolve(__dirname,'../../docs/dafny-editor-audit.json'),'utf8'));
  assert.deepEqual(validateIndex(audit),[]);if(require('../parity/inventory.cjs').checkOffline().mode==='full')assert.deepEqual(validate(audit),[]);else assert.throws(()=>validate(audit),/Full parity inventory unavailable/);audit.testFiles[0].cases.push({id:'fake',status:'complete',runtimeEvidence:[]});
  assert.ok(validateIndex(audit).length);
});
test('unsupported and untested capabilities cannot be marked complete',()=>{
  const inventory=require('./parity-fixture.cjs').inventoryFixture();
  assert.deepEqual(validate(inventory),[]);
  inventory.features[0].assessment.status='complete';assert.ok(validate(inventory).some(e=>e.includes('unsupported completeness')));
  inventory.features[0].assessment.testEvidence=[{status:'skipped',assertion:'something',artifact:'fake.json'}];
  assert.ok(validate(inventory).some(e=>e.includes('unsupported completeness')));
});
test('inventory shrinkage and invented upstream evidence fail the offline gate',()=>{
  const original=require('./parity-fixture.cjs').inventoryFixture();
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
    const run=await launch(config,{code,operationTimeoutMs:1000,timeoutMs:2000,obligations:1,resourceState:admitted});
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
    const run=await launch(config,{code,operationTimeoutMs:1000,timeoutMs:2000,obligations:1,resourceState:admitted});
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
    const run=await launch(config,{code,operationTimeoutMs:1000,timeoutMs:3000,obligations:1,resourceState:admitted});
    pid=Number(readFileSync(pidfile,'utf8'));
    assert.ok(run.resources.cleanup.terminatedOwnedSurvivors.some(p=>p.pid===pid));
    assert.deepEqual(run.resources.cleanup.remaining,[]);assert.equal(run.status,'passed');
  }finally{if(pid)try{process.kill(pid,'SIGKILL');}catch{}rmSync(dir,{recursive:true,force:true});}
});
test('the launcher refuses before spawning when the injected snapshot has swap or too little memory',async()=>{
  if(process.platform!=='linux')return;
  for(const snapshot of [{availableBytes:16*1024**3,swapTotalBytes:1024},{availableBytes:12*1024**3-1,swapTotalBytes:0}]){
    const dir=mkdtempSync(join(tmpdir(),'parity-admission-'));
    try {
      const code=join(dir,'code'),marker=join(dir,'spawned');
      writeFileSync(code,`#!/bin/sh\ntouch ${JSON.stringify(marker)}\n`,{mode:0o700});
      const trial=join(dir,'trial');
      const config={dir:trial,target:'local',workers:1,cache:'none',trial:0,warmup:false,workspace:join(trial,'workspace'),result:join(trial,'result.json'),events:join(trial,'events.jsonl'),trace:join(trial,'lsp.jsonl')};
      await assert.rejects(launch(config,{code,operationTimeoutMs:1000,timeoutMs:2000,obligations:1,resourceState:()=>snapshot}),/resource admission denied before launch/);
      assert.equal(require('node:fs').existsSync(marker),false,'no editor spawned');
      assert.deepEqual(JSON.parse(readFileSync(join(trial,'resource-admission.json'),'utf8')).snapshot,snapshot);
    }finally{rmSync(dir,{recursive:true,force:true});}
  }
});
test('long artifact paths do not become long editor IPC/profile paths',async()=>{
  if(process.platform==='win32')return;
  const dir=mkdtempSync(join(tmpdir(),'parity-path-'));
  try {
    const code=join(dir,'code'),record=join(dir,'launch.json');
    writeFileSync(code,`#!${process.execPath}\nrequire('node:fs').writeFileSync(${JSON.stringify(record)},JSON.stringify({portable:process.env.VSCODE_PORTABLE,args:process.argv}));\n`,{mode:0o700});
    const trial=join(dir,'long-artifacts-'.repeat(12));
    const config={dir:trial,target:'local',workers:1,cache:'none',trial:0,warmup:false,workspace:join(trial,'workspace'),result:join(trial,'result.json'),events:join(trial,'events.jsonl'),trace:join(trial,'lsp.jsonl')};
    await launch(config,{code,operationTimeoutMs:1000,timeoutMs:2000,obligations:1,resourceState:admitted});
    const data=JSON.parse(readFileSync(record,'utf8'));
    assert.ok(join(data.portable,'user-data/1.10-main.sock').length<107);
    assert.equal(data.portable.startsWith(trial),false);
    assert.equal(require('node:fs').existsSync(data.portable),false,'temporary editor state is removed');
  }finally{rmSync(dir,{recursive:true,force:true});}
});


test('visual suite retains all phase gaps without requiring the separate benchmark scenario',()=>{
  const config={runId:'visual-fresh',target:'dafny',suite:'visual'};
  const ids=['visual-open','visual-first-feedback','visual-verified','visual-proof-broken','visual-proof-fixed'];
  const base={schemaVersion:1,runId:config.runId,target:config.target,status:'passed-with-gaps',checks:[],
    scenarios:ids.map(id=>({id,status:id==='visual-open'?'missing':'partial'}))};
  assert.deepEqual(hostEvidenceErrors(base,config),[]);
  for(const id of ids)assert.ok(hostEvidenceErrors({...base,scenarios:base.scenarios.filter(s=>s.id!==id)},config).length,'missing '+id+' cannot pass report validation');
  assert.ok(hostEvidenceErrors({...base,status:'passed'},config).length,'visual gaps cannot become a pass');
  assert.ok(hostEvidenceErrors({...base,runId:'stale'},config).length);
  assert.ok(hostEvidenceErrors({...base,checks:['visual-verified']},config).length,'partial phases are not passed checks');
  assert.ok(hostEvidenceErrors(base,{...config,suite:'full'}).length,'full suite still requires initial verification');
});


test('visual launcher passes suite identity to report validation (injected editor)',async()=>{
  if(process.platform==='win32')return;
  const dir=mkdtempSync(join(tmpdir(),'parity-visual-suite-'));
  try {
    const code=join(dir,'code');
    writeFileSync(code,`#!${process.execPath}\nconst fs=require('node:fs');const c=JSON.parse(fs.readFileSync(process.env.PARITY_HOST_CONFIG,'utf8'));fs.writeFileSync(c.result,JSON.stringify({schemaVersion:1,runId:c.runId,target:c.target,status:'passed-with-gaps',checks:[],scenarios:['visual-open','visual-first-feedback','visual-verified','visual-proof-broken','visual-proof-fixed'].map(id=>({id,status:'missing'}))}));\n`,{mode:0o700});
    const trial=join(dir,'trial');
    const config={dir:trial,target:'local',workers:1,cache:'basic',trial:0,warmup:false,workspace:join(trial,'workspace'),result:join(trial,'result.json'),events:join(trial,'events.jsonl'),trace:join(trial,'lsp.jsonl')};
    const run=await launch(config,{code,suite:'visual',operationTimeoutMs:1000,timeoutMs:2000,obligations:1,resourceState:admitted});
    assert.equal(run.status,'passed-with-gaps');assert.equal(run.result.scenarios.every(s=>s.status==='missing'),true);assert.deepEqual(run.result.checks,[]);
  }finally{rmSync(dir,{recursive:true,force:true});}
});

test('compiler command suite cannot masquerade as full proof evidence',()=>{
 const config={runId:'commands-only',target:'local',suite:'commands'},report={schemaVersion:1,runId:config.runId,target:'local',status:'passed',checks:['command-build-keybinding'],scenarios:[{id:'command-build-keybinding',status:'passed'}]};
 assert.deepEqual(hostEvidenceErrors(report,config),[]);assert.ok(hostEvidenceErrors(report,{...config,suite:'full'}).length);assert.ok(hostEvidenceErrors({...report,scenarios:[]},config).length);assert.ok(hostEvidenceErrors({...report,runId:'old'},config).length);assert.ok(hostEvidenceErrors({...report,checks:[]},config).length);
 assert.throws(()=>parse(['--suite','commands','--targets','dafny']),/requires --targets local/);assert.equal(parse(['--suite','commands','--targets','local']).suite,'commands');
});
test('native build key dispatch refuses an unfocused editor (injected CDP boundary)',async()=>{
 const {buildKeybinding}=require('../parity/renderer.cjs'),calls=[];
 await assert.rejects(buildKeybinding({request:async(method,params)=>{calls.push({method,params});return{result:{value:false}};}}),/No focused source editor/);assert.equal(calls.length,1);
 calls.length=0;const value=await buildKeybinding({request:async(method,params)=>{calls.push({method,params});return{result:{value:true}};}});assert.equal(value.chord,'ctrl+shift+b');assert.deepEqual(calls.slice(1).map(c=>[c.method,c.params.type,c.params.code,c.params.modifiers]),[['Input.dispatchKeyEvent','keyDown','KeyB',10],['Input.dispatchKeyEvent','keyUp','KeyB',10]]);
});

test('context submenu observation refuses to click without a source editor (injected CDP boundary)',async()=>{
 const {contextSubmenu}=require('../parity/renderer.cjs'),calls=[];await assert.rejects(contextSubmenu({request:async(method,params)=>{calls.push({method,params});return{result:{value:null}};}},'/unused'),/No source editor/);assert.equal(calls.length,1);assert.equal(calls[0].method,'Runtime.evaluate');
});

for(const suite of ['custom-commands','custom-default-commands'])test(suite+' requires its own native action and cannot replace proof evidence',()=>{
 const id=suite==='custom-commands'?'command-custom-build-keybinding':'command-custom-default-build-keybinding';
 const config={runId:'custom-only',target:'local',suite},report={schemaVersion:1,runId:config.runId,target:'local',status:'passed',checks:[id],scenarios:[{id,status:'passed'}]};
 assert.deepEqual(hostEvidenceErrors(report,config),[]);assert.ok(hostEvidenceErrors(report,{...config,suite:'full'}).length);assert.ok(hostEvidenceErrors({...report,scenarios:[{id:'command-build-keybinding',status:'passed'}],checks:['command-build-keybinding']},config).length);
 assert.equal(parse(['--suite',suite,'--targets','local']).suite,suite);
});
test('F6 refuses wrong prompt contents before Enter (injected CDP boundary)',async()=>{
 const {buildKeybinding}=require('../parity/renderer.cjs'),calls=[];let evaluations=0;
 await assert.rejects(buildKeybinding({request:async(method,params)=>{calls.push({method,params});if(method==='Runtime.evaluate')return{result:{value:++evaluations===1?true:{focused:true,value:'wrong'}}};return{};}},{custom:true,input:'{}'}),/contents did not match/);
 assert.deepEqual(calls.filter(c=>c.params.code==='F6').map(c=>[c.params.type,c.params.modifiers]),[['keyDown',0],['keyUp',0]]);assert.equal(calls.some(c=>c.params.code==='Enter'),false);
});
test('terminal observer retains real output/exit and stops subscriptions on restore (injected VS Code boundary)',async()=>{
 let start,end,disposed=0;const records=[],vscode={tests:{},window:{onDidStartTerminalShellExecution:f=>(start=f,{dispose(){disposed++;}}),onDidEndTerminalShellExecution:f=>(end=f,{dispose(){disposed++;}})},languages:{onDidChangeDiagnostics:()=>({dispose(){}})}};
 const observer=observe(vscode,(kind,data)=>records.push({kind,data}),'/not-an-extension',null,'/owned/workspace');
 try{assert.equal(observer.terminalSupported,true);const execution={commandLine:{value:'build /owned/workspace/main.dfy'},async *read(){yield 'compiler output';}};start({execution});end({execution,exitCode:3});await new Promise(r=>setImmediate(r));assert.equal(records.find(r=>r.kind==='terminal.end').data.exitCode,3);assert.equal(records.find(r=>r.kind==='terminal.output').data.data,'compiler output');assert.ok(records.some(r=>r.kind==='terminal.output.end'));const length=records.length;start({execution:{...execution,commandLine:{value:'build /other/file'}}});await new Promise(r=>setImmediate(r));assert.equal(records.length,length);}finally{observer.restore();}assert.equal(disposed,2);
});

test('paired default custom suite cannot omit its partial native trace observation',()=>{
 const id='command-custom-default-build-keybinding',config={runId:'pair',target:'dafny',suite:'custom-default-commands'},report={schemaVersion:1,...config,status:'passed',checks:[id],scenarios:[{id,status:'passed'}]};
 assert.ok(hostEvidenceErrors(report,config).includes('missing native observation native-trace-show-copy-hide'));
 assert.deepEqual(hostEvidenceErrors({...report,status:'passed-with-gaps',scenarios:[...report.scenarios,...['native-trace-show-copy-hide','native-dafny-run-action','native-dafny-test-action','native-trace-lifecycle'].map(id=>({id,status:'partial'}))]},config),[]);
});
test('terminal execution IDs cannot combine output and exit from distinct executions (injected boundary)',async()=>{
 let start,end;const records=[],vscode={tests:{},window:{onDidStartTerminalShellExecution:f=>(start=f,{dispose(){}}),onDidEndTerminalShellExecution:f=>(end=f,{dispose(){}})},languages:{onDidChangeDiagnostics:()=>({dispose(){}})}};
 const observer=observe(vscode,(kind,data)=>records.push({kind,data}),'/unused',null,'/owned');
 try{const make=()=>({commandLine:{value:'build /owned/main.dfy'},async *read(){yield 'data';}}),a=make(),b=make();start({execution:a});start({execution:b});end({execution:b,exitCode:3});end({execution:a,exitCode:0});await new Promise(r=>setImmediate(r));const starts=records.filter(r=>r.kind==='terminal.start');assert.notEqual(starts[0].data.executionId,starts[1].data.executionId);for(const [executionId,exit] of [[starts[0].data.executionId,0],[starts[1].data.executionId,3]]){assert.equal(records.find(r=>r.kind==='terminal.end'&&r.data.executionId===executionId).data.exitCode,exit);assert.ok(records.some(r=>r.kind==='terminal.output.end'&&r.data.executionId===executionId));}observer.restore();const length=records.length;start({execution:a});end({execution:a,exitCode:0});assert.equal(records.length,length);}finally{observer.restore();}
});

test('terminal SDK observation strips native shell control sequences but rejects suffix paths or wrong versions',()=>{
 const {terminalSdkIdentity}=require('../parity/core.cjs'),raw='\x1b]633;C\x07'+process.execPath+'\r\n\x1b[?1h\x1b='+process.version+'\r\n';
 const observed=terminalSdkIdentity(raw,process.execPath,process.version);assert.equal(observed.executable,require('node:fs').realpathSync(process.execPath));assert.match(observed.sha256,/^[a-f0-9]{64}$/);assert.throws(()=>terminalSdkIdentity('/other'+process.execPath+'\n'+process.version,process.execPath,process.version),/differs/);assert.throws(()=>terminalSdkIdentity(process.execPath+'\nwrong',process.execPath,process.version),/differs/);
});

test('native trace visibility suite stays distinct from local or full proof evidence',()=>{
 assert.equal(parse(['--suite','trace-visibility','--targets','dafny']).suite,'trace-visibility');assert.throws(()=>parse(['--suite','trace-visibility','--targets','local']),/requires --targets dafny/);
 const config={suite:'trace-visibility',target:'dafny',runId:'native'},report={schemaVersion:1,runId:'native',target:'dafny',status:'passed-with-gaps',checks:[],scenarios:[{id:'native-trace-tab-visibility-theme',status:'partial'}]};assert.deepEqual(hostEvidenceErrors(report,config),[]);assert.ok(hostEvidenceErrors(report,{...config,suite:'full'}).length);assert.ok(hostEvidenceErrors({...report,scenarios:[]},config).length);
});

test('explicit native light-show observation cannot replace theme continuity, lifecycle or proof scenarios',()=>{
 assert.equal(parse(['--suite','trace-light-show','--targets','dafny']).suite,'trace-light-show');assert.throws(()=>parse(['--suite','trace-light-show','--targets','local']),/requires --targets dafny/);const config={suite:'trace-light-show',target:'dafny',runId:'light'},report={schemaVersion:1,runId:'light',target:'dafny',status:'passed-with-gaps',checks:[],scenarios:[{id:'native-trace-light-show-hide',status:'partial'}]};assert.deepEqual(hostEvidenceErrors(report,config),[]);for(const suite of ['full','custom-default-commands','trace-visibility'])assert.ok(hostEvidenceErrors(report,{...config,suite}).length);
});

test('native compiler-only import suite retains exact action ownership and cannot replace full parity',()=>{
 const id='command-custom-import-actions',config={runId:'imports',target:'local',suite:'custom-import-actions'},source='import "alias/Dependency.sol";',hash=require('node:crypto').createHash('sha256').update(source).digest('hex'),prompt={before:{value:JSON.stringify({includePaths:['vendor with spaces'],remappings:['alias/=lib/']})},submitted:{value:JSON.stringify({includePaths:['vendor with spaces'],remappings:['alias/=lib/']})},rendered:{screenshot:true}},request={runId:config.runId,observation:{contextMenu:{rendered:{screenshot:true}},prompt}},started={phase:'started',operation:'buildCustomArgs',commandId:'own',sourceSession:1,uri:'file:///fixture/commands.sol',version:2,sourceHash:hash},completed={phase:'completed',uri:'file:///fixture/commands.sol',version:2,sourceHash:hash,commandId:'own',sourceSession:1,artifact:'/actual/compiler.ast.json'},observation={source,version:2,request,report:{operation:'buildCustomArgs',kind:'compiler-ast',outputDirectory:'/fixture/bin',verification:'not-run',source:'/fixture/commands.sol',compilerOptions:{includePaths:['vendor with spaces'],remappings:['alias/=lib/']},sourceHash:hash,artifact:completed.artifact},commandOwnership:{started,completed}},report={schemaVersion:1,...config,status:'passed',checks:[id],scenarios:[{id,status:'passed',observation}],observations:{customCancellation:{source:'previous snapshot',sourceHash:require('node:crypto').createHash('sha256').update('previous snapshot').digest('hex'),version:1,trusted:true,request:{runId:config.runId,observation:{prompt:{cancelled:{rendered:{screenshot:true}}}}}}}};
 assert.ok(hostEvidenceErrors(report,config).some(e=>e.includes('custom input refusal')),'native import evidence without invalid F6 observations must refuse');
 report.observations.customInputRefusals=['syntax','options'].map(kind=>require('./custom-input-fixture.cjs').refusal(kind,config.runId));
 assert.deepEqual(hostEvidenceErrors(report,config),[]);for(const change of [r=>r.scenarios[0].observation.report.operation='build',r=>r.scenarios[0].observation.commandOwnership.completed.sourceSession=0,r=>delete r.observations.customCancellation,r=>r.observations.customCancellation.request.runId='old',r=>delete r.scenarios[0].observation.report,r=>r.scenarios[0].observation.report.sourceHash='wrong',r=>delete r.scenarios[0].observation.request.observation.contextMenu]){const bad=structuredClone(report);change(bad);assert.ok(hostEvidenceErrors(bad,config).length);}
 assert.ok(hostEvidenceErrors(report,{...config,suite:'full'}).length);assert.equal(parse(['--suite','custom-import-actions','--targets','local,dafny']).suite,'custom-import-actions');
 const fixture=require('../parity/workloads.cjs').customImportWorkload('local');assert.match(fixture.source,/alias\/Dependency.sol/);assert.ok(!fixture.source.includes('@custom:key'));assert.ok(require('../parity/workloads.cjs').workload('local',1).includes('@custom:key'),'original annotated workload remains unchanged');
});

test('native request polling records partial/malformed identity and recovers for a fresh request',()=>{
 const fs=require('node:fs'),os=require('node:os'),path=require('node:path'),{readKeybindingRequest}=require('../parity/run.cjs'),dir=fs.mkdtempSync(path.join(os.tmpdir(),'native-key-request-')),file=path.join(dir,'request.json');
 try{assert.ok(readKeybindingRequest(file).error);for(const partial of ['', '{', '{}']){fs.writeFileSync(file,partial);assert.ok(readKeybindingRequest(file).error);}const request={runId:'native',requestId:'second'};fs.writeFileSync(file,JSON.stringify(request));assert.deepEqual(readKeybindingRequest(file),{request});const seen=new Set();assert.deepEqual(readKeybindingRequest(file,seen),{request});assert.deepEqual(readKeybindingRequest(file,seen),{ignored:true});const next={runId:'native',requestId:'third'};require('../parity/phase-capture.cjs').atomicJson(file,next);assert.equal(fs.existsSync(file+'.tmp'),false);assert.deepEqual(readKeybindingRequest(file,seen),{request:next});fs.writeFileSync(file,JSON.stringify(request));assert.deepEqual(readKeybindingRequest(file,seen),{ignored:true});}finally{fs.rmSync(dir,{recursive:true,force:true});}
});

// Guard regression: malformed status evidence must not crash analysis or certify timing.
test('malformed symbol status recordings are broken evidence rather than observer exceptions',()=>{
 const dir=mkdtempSync(join(tmpdir(),'parity-symbol-malformed-')),file=join(dir,'lsp.jsonl'),range={start:{line:0,character:0},end:{line:0,character:1}},valid={uri:'file:///a.dfy',namedVerifiables:[{nameRange:range,status:1}]};
 try{for(const params of [null,{}, {...valid,namedVerifiables:null},{...valid,namedVerifiables:[null]},{...valid,namedVerifiables:[{nameRange:range,status:3}]},{...valid,namedVerifiables:[{nameRange:{start:{line:2,character:0},end:{line:1,character:0}},status:1}]}]){writeFileSync(file,JSON.stringify({direction:'server',time:1,message:{method:'dafny/textDocument/symbolStatus',params}}));const result=protocol(file);assert.equal(result.status,'broken');assert.ok(result.errors.length);assert.equal(result.queueMs.n,0);}
 writeFileSync(file,[1,2,5].map((status,i)=>JSON.stringify({direction:'server',time:i+1,message:{method:'dafny/textDocument/symbolStatus',params:{...valid,namedVerifiables:[{nameRange:range,status}]}}})).join('\n'));const result=protocol(file);assert.equal(result.status,'partial');assert.equal(result.queueMs.median,1);assert.equal(result.symbolExecutionMs.median,1);
 }finally{rmSync(dir,{recursive:true,force:true});}
});

// Guard regression: transport direction and monotonic observations are prerequisites for latency evidence.
test('wrong-direction and backwards status clocks cannot certify symbol latency',()=>{
 const dir=mkdtempSync(join(tmpdir(),'parity-symbol-clock-')),file=join(dir,'lsp.jsonl'),params=status=>({uri:'file:///clock.dfy',version:7,namedVerifiables:[{status,nameRange:{start:{line:0,character:0},end:{line:0,character:1}}}]}),packet=(status,time,direction='server')=>({direction,time,message:{method:'dafny/textDocument/symbolStatus',params:params(status)}});
 try{for(const rows of [[packet(1,1,'client')],[packet(1,2),packet(2,1)],[packet(2,2),packet(5,1)]]){writeFileSync(file,rows.map(r=>JSON.stringify(r)).join('\n'));const result=protocol(file);assert.equal(result.status,'broken');assert.ok(result.errors.length);assert.equal(result.queueMs.n,0);assert.equal(result.symbolExecutionMs.n,0);}}finally{rmSync(dir,{recursive:true,force:true});}
});

// Guard regression: an output scenario name alone cannot certify native channel/source lifecycle.
test('native output lifecycle requires retained channel, current source and ordered readiness',()=>{
 const {outputLifecycleErrors}=require('../parity/core.cjs'),uri='file:///output.sol',sourceText='contract C {}',sourceHash=require('node:crypto').createHash('sha256').update(sourceText).digest('hex'),source={uri,version:1,textHash:sourceHash,session:'actual-session',trusted:true,closed:false},channel={kind:'output.create',data:{channel:'Solidity Lean',channelId:1}},line=text=>({kind:'output',data:{channel:'Solidity Lean',channelId:1,text}}),o={uri,version:1,sourceHash,channel,channels:[channel],startup:line('Solidity Lean is ready for '+uri+' (language services; version 1.0.0).'),events:[{kind:'command.start',data:{id:'solidityLean.restartServer',invocationId:2,source}},line('Terminating Solidity Lean language services...'),line('Solidity Lean is ready again for '+uri+' (language services; version 1.0.0).'),{kind:'command.end',data:{id:'solidityLean.restartServer',invocationId:2,source}}]};
 channel.ms=0;o.startup.ms=1;o.events.forEach((event,i)=>event.ms=i+2);assert.deepEqual(outputLifecycleErrors(o,'local'),[]);for(const key of ['uri','channel','channels','startup','events']){const bad=structuredClone(o);delete bad[key];assert.ok(outputLifecycleErrors(bad,'local').length,key);}
 for(const mutate of [b=>b.startup.ms=99,b=>b.events.reverse(),b=>b.events=[b.events[1],b.events[2],b.events[0],b.events[3]],b=>b.events[2].data.channelId=7,b=>b.events[2].data.text=b.events[2].data.text.replace(uri,'file:///foreign.sol'),b=>b.channels.push({kind:'output.dispose',data:channel.data}),b=>b.events[3].data.source={...b.events[3].data.source,session:'reopened'},b=>b.channel={kind:'output.create'}]){const bad=structuredClone(o);mutate(bad);assert.ok(outputLifecycleErrors(bad,'local').length);}
 assert.equal(parse(['--suite','output-lifecycle']).suite,'output-lifecycle');const config={suite:'output-lifecycle',target:'local',runId:'run'},report={schemaVersion:1,runId:'run',target:'local',status:'passed-with-gaps',checks:[],scenarios:[{id:'native-output-restart',status:'partial',observation:o}]};assert.ok(hostEvidenceErrors(report,config).length,'API-only receipt cannot satisfy rendered output suite');const readinessPrefix='Solidity Lean is ready again',metadata={uri,version:1,sourceHash,sourceSession:'actual-session',channelId:1,channel:'Solidity Lean',readinessPrefix,readinessLine:o.events[2].data.text};o.panel={runId:'run',phase:'output-channel',status:'captured',metadataHash:require('node:crypto').createHash('sha256').update(JSON.stringify(metadata)).digest('hex'),capture:{captured:true,screenshot:true,output:{panelVisible:true,readinessVisibility:'not-certified',glyphGeometry:{before:require('./output-visibility-fixture.cjs').sample(metadata.readinessLine),after:require('./output-visibility-fixture.cjs').sample(metadata.readinessLine)},selectedChannel:'Solidity Lean',text:metadata.readinessLine,before:{visible:true,selectedChannel:'Solidity Lean',continuousText:metadata.readinessLine},after:{visible:true,selectedChannel:'Solidity Lean',continuousText:metadata.readinessLine}}}};assert.ok(hostEvidenceErrors(report,config).length,'local shutdown evidence remains required');o.shutdown={ownerPid:42,events:[{kind:'output.shutdown.close',data:{pid:43,birth:'123'}},{kind:'output.dispose',data:channel.data}],children:[{pid:43,birth:'123',before:{birth:'123',ppid:42,group:43,session:43},confirmedClose:true,afterGroup:[],workers:[]}]};o.feedback={identity:{serverInfo:{name:'Owned server',version:'1.0.0'},runtimeInfo:{version:'v22.0.0'}}};o.feedback.url=require('../src/status-summary.cjs').issueURL(o.feedback.identity);o.events[2].data.text+='\nIf you have time, report why restart was needed:\n'+o.feedback.url;o.resourceLifecycle={runtimeBefore:'/actual/node',rejectedRuntime:'/missing/node',runtimeRestored:'/actual/node',runtimeBeforeReported:{configuredPath:'/actual/node',version:'24.19.0'},runtimeRecoveredReported:{configuredPath:'/actual/node',version:'24.19.0'},failureEvents:[line('Language server startup failed for '+uri+': /missing/node ENOENT')],recoveryEvents:[line(o.events[2].data.text)],reopen:{beforeSynchronizationId:'1',afterSynchronizationId:'2',beforeOpenRecord:{direction:'client',message:{method:'textDocument/didOpen',params:{textDocument:{uri,version:1,text:sourceText,synchronizationId:'1'}}}},beforeSession:'old',afterSession:'new',closeIndex:1,openIndex:2,closeRecord:{direction:'client',message:{method:'textDocument/didClose',params:{textDocument:{uri}}}},openRecord:{direction:'client',message:{method:'textDocument/didOpen',params:{textDocument:{uri,version:1,text:sourceText,synchronizationId:'2'}}}}}};assert.deepEqual(hostEvidenceErrors(report,config),[]);for(const mutate of [o=>delete o.feedback,o=>o.feedback.url='https://example.invalid/wrong',o=>o.feedback.identity.serverInfo.version='foreign']){const bad=structuredClone(report);mutate(bad.scenarios[0].observation);assert.ok(hostEvidenceErrors(bad,config).length);}for(const mutate of [s=>s.children[0].confirmedClose=false,s=>s.children[0].afterGroup=[{pid:43}],s=>s.events.reverse(),s=>s.children[0].before.birth='stale']){const bad=structuredClone(report);mutate(bad.scenarios[0].observation.shutdown);assert.ok(hostEvidenceErrors(bad,config).length);}for(const mutate of [l=>l.runtimeRestored='/wrong/node',l=>l.failureEvents.push(line('Solidity Lean is ready again for '+uri+' (wrong)')),l=>l.runtimeRecoveredReported.configuredPath='/foreign/node',l=>l.reopen.afterSynchronizationId=l.reopen.beforeSynchronizationId,l=>l.reopen.afterSession=l.reopen.beforeSession,l=>l.reopen.openRecord.message.params.textDocument.text='foreign']){const bad=structuredClone(report);mutate(bad.scenarios[0].observation.resourceLifecycle);assert.ok(hostEvidenceErrors(bad,config).length);}const multi=structuredClone(report);multi.scenarios[0].observation.events.splice(2,0,{...o.events[2],data:{...o.events[2].data,text:o.events[2].data.text.replace(uri,'file:///foreign.sol')}});assert.deepEqual(hostEvidenceErrors(multi,config),[],'foreign earlier readiness cannot change target binding');for(const mutate of [p=>p.runId='foreign',p=>p.metadataHash='wrong',p=>p.capture.output.panelVisible=false,p=>p.capture.output.text='wrong nonempty output',p=>p.capture.output.selectedChannel='Foreign',p=>p.capture.output.after.selectedChannel='Foreign',p=>p.capture.output.after.visible=false,p=>p.capture.output.after.continuousText=p.capture.output.after.continuousText.replace(uri,'file:///foreign.sol'),p=>p.capture.screenshot=false]){const bad=structuredClone(report);mutate(bad.scenarios[0].observation.panel);assert.ok(hostEvidenceErrors(bad,config).length);}assert.ok(hostEvidenceErrors({...report,scenarios:[{id:'native-output-restart',status:'partial'}]},config).length);
});
