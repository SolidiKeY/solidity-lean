#!/usr/bin/env node
'use strict';
const {spawn,spawnSync} = require('node:child_process');
const {mkdirSync,mkdtempSync,readFileSync,writeFileSync,existsSync,rmSync,openSync,closeSync,cpSync} = require('node:fs');
const {resolve,join,dirname} = require('node:path');
const {tmpdir,cpus,totalmem,release} = require('node:os');
const {performance} = require('node:perf_hooks');
const {randomUUID,createHash} = require('node:crypto');
const {ProcessSampler,summarize,differences,normalize,scaling,protocol} = require('./core.cjs');
const {terminateTree} = require('../src/backend.cjs');
const renderer=require('./renderer.cjs');
const repo=resolve(__dirname,'../..');

function parse(args) {
  const options={trials:5,warmups:1,workers:[1,2,4],obligations:8,timeoutMs:300000,operationTimeoutMs:60000,targets:['dafny','local'],cache:['none','basic'],trace:'on',suite:'full'};
  const keys={'--code':'code','--dafny':'dafny','--dafny-extension':'dafnyExtension','--dotnet':'dotnet','--output':'output',
    '--trials':'trials','--warmups':'warmups','--workers':'workers','--obligations':'obligations','--timeout-ms':'timeoutMs','--operation-timeout-ms':'operationTimeoutMs','--targets':'targets','--cache':'cache','--trace':'trace',
    '--memory-reserve-mib':'memoryReserveMiB','--memory-max-mib':'memoryMaxMiB','--suite':'suite'};
  for(let i=0;i<args.length;i++) {
    if(args[i]==='--help') return {help:true};
    const key=keys[args[i]];if(!key||!args[i+1]||args[i+1].startsWith('--')) throw new Error('Invalid option '+args[i]);
    let value=args[++i];
    if(['trials','warmups','obligations','timeoutMs','operationTimeoutMs','memoryReserveMiB','memoryMaxMiB'].includes(key)) value=Number(value);
    if(['workers','targets','cache'].includes(key)) value=value.split(',').map(v=>key==='workers'?Number(v):v);
    options[key]=value;
  }
  for(const key of ['trials','warmups','obligations','timeoutMs','operationTimeoutMs']) if(!Number.isSafeInteger(options[key])||options[key]<(key==='warmups'?0:1)) throw new Error('Invalid '+key);
  if(options.workers.some(v=>!Number.isSafeInteger(v)||v<1||v>32)) throw new Error('Invalid workers');
  if(options.targets.some(t=>!['dafny','local'].includes(t))) throw new Error('Invalid target');
  if(options.cache.some(t=>!['none','basic','advanced'].includes(t))) throw new Error('Invalid cache');
  for(const key of ['workers','targets','cache'])if(new Set(options[key]).size!==options[key].length)throw new Error('Duplicate '+key);
  if(options.obligations>1000||options.trials>100||options.warmups>10)throw new Error('Excessive benchmark dimensions');
  if(!['on','off'].includes(options.trace))throw new Error('Invalid trace');
  if(!['full','benchmark'].includes(options.suite))throw new Error('Invalid suite');
  for(const key of ['memoryReserveMiB','memoryMaxMiB'])if(options[key]!==undefined&&(!Number.isSafeInteger(options[key])||options[key]<1))throw new Error('Invalid '+key);
  return options;
}
function git(directory) {return spawnSync('git',['-C',directory,'rev-parse','HEAD'],{encoding:'utf8'}).stdout?.trim()||null;}
function shortSummary(report) {
  const lines=['# Editor parity run','',`Status: **${report.status}**. Full parity: **not established**.`,
    '',`Node ${report.environment.node}; ${report.environment.cpu}; ${report.environment.logicalCpus} logical CPUs; ${report.environment.memoryBytes} bytes RAM.`,
    '', 'Trials run sequentially. Each launch has an isolated profile/workspace. Process-cold startup retains operating-system caches; warm incremental edits reuse the live server.',
    '', '| Target | Workers requested | Cache requested | Trials | Failures | Initial median ms | Initial p95 ms | Peak RSS median bytes |',
    '|---|---:|---|---:|---:|---:|---:|---:|'];
  for(const s of report.summary) lines.push(`| ${s.target} | ${s.workers} | ${s.cache} | ${s.trials} | ${s.failures} | ${s.metrics.initialVerificationMs?.median?.toFixed(1)??'unmeasured'} | ${s.metrics.initialVerificationMs?.p95?.toFixed(1)??'unmeasured'} | ${s.peakRssBytes.median??'unmeasured'} |`);
  lines.push('','Local backend has no verification worker/cache setting. Requested values are recorded as unsupported, never treated as applied.',
    '', '## Parallel scaling','', '| Target | Cache | Workers | Speedup | Efficiency |','|---|---|---:|---:|---:|',
    ...(report.parallelScaling||[]).map(s=>`| ${s.target} | ${s.cache} | ${s.workers} | ${s.speedup?.toFixed(3)??'unsupported'} | ${s.efficiency?.toFixed(3)??'unsupported'} |`));
  const grouped=new Map();
  for(const c of report.comparisons){if(!grouped.has(c.scenario))grouped.set(c.scenario,{comparisons:0,differences:0});const group=grouped.get(c.scenario);group.comparisons++;group.differences+=c.differences.length;}
  const counts={};for(const feature of report.featureParity||[])counts[feature.status]=(counts[feature.status]||0)+1;
  lines.push('', '## Feature audit','',Object.entries(counts).map(([k,v])=>`${k}: ${v}`).join('; ')+'. Runtime evidence is attached per feature in report.json.',
    '', '## Differences','',...[...grouped].map(([scenario,c])=>`- ${scenario}: ${c.differences} native observable differences across ${c.comparisons} paired trials.`),
    '', '## Limits','',...report.limitations.map(x=>'- '+x),'');
  return lines.join('\n');
}
async function launch(config,options) {
  config={...config,runId:randomUUID()};
  mkdirSync(config.dir,{recursive:true});mkdirSync(config.workspace,{recursive:true});
  const cache={'none':'No caching',basic:'Basic caching',advanced:'Advanced caching'}[config.cache];
  const settings= config.target==='dafny' ? {'dafny.version':'custom','dafny.cliPath':resolve(options.dafny),'dafny.dotnetExecutablePath':resolve(options.dotnet),
    'dafny.verificationVirtualCores':config.workers,'dafny.verificationCachingPolicy':cache,'dafny.verificationTimeLimit':20,
    'dafny.automaticVerification':'onchange','dafny.displayGutterStatus':true,'dafny.markGhostStatements':true} : {
    'solidityLean.backendPath':repo,'solidityLean.nodePath':process.execPath,'solidityLean.timeoutMs':options.operationTimeoutMs};
  settings['files.autoSave']='off';settings['telemetry.telemetryLevel']='off';settings['update.mode']='none';
  settings['git.enabled']=false;settings['workbench.secondarySideBar.defaultVisibility']='hidden';
  mkdirSync(join(config.workspace,'.vscode'),{recursive:true});
  writeFileSync(join(config.workspace,'.vscode/settings.json'),JSON.stringify(settings));
  const runtimeEnvironment=Object.fromEntries(['PATH','SOLKEY_ROOT','LEAN_NUM_THREADS','XDG_CACHE_HOME'].filter(k=>process.env[k]!==undefined).map(k=>[k,process.env[k]]));
  const hostConfig={...config,suite:options.suite||'full',runtimeEnvironment,recordProtocol:options.trace!=='off'&&config.target==='dafny',obligations:options.obligations,operationTimeoutMs:options.operationTimeoutMs};
  const configPath=join(config.dir,'config.json');writeFileSync(configPath,JSON.stringify(hostConfig));
  const extension=config.target==='local'?resolve(repo,'vscode'):resolve(options.dafnyExtension);
  const logfile=openSync(join(config.dir,'editor.log'),'w');
  const debugPort=await renderer.availablePort();
  // VS Code's Unix socket path is limited to 107 bytes. Artifact paths may be
  // arbitrarily deep, so editor state must live under a short temporary root.
  const editorState=mkdtempSync(join(tmpdir(),'slp-'));
  const portable=join(editorState,'p');mkdirSync(portable,{recursive:true});writeFileSync(join(portable,'argv.json'),'{}');
  const start=performance.now(),launchedWallTime=Date.now();
  const child=spawn(resolve(options.code),[config.workspace,'--disable-gpu','--disable-workspace-trust','--skip-welcome','--skip-release-notes','--no-sandbox',
    '--disable-updates','--remote-debugging-port='+debugPort,'--user-data-dir',join(editorState,'u'),'--extensions-dir',join(editorState,'e'),
    '--extensionDevelopmentPath='+extension,'--extensionTestsPath='+join(__dirname,'host.cjs')],{
    cwd:repo,detached:process.platform!=='win32',stdio:['ignore',logfile,logfile],
    env:{...process.env,VSCODE_CLI:'1',VSCODE_PORTABLE:portable,PARITY_HOST_CONFIG:configPath}});
  const sampler=new ProcessSampler(child.pid);
  let timedOut=false,interrupted=false,resourceStop=false,rendererClient,rendererCapture,rendering=false,probe,probing=false,probeTask,captureTask;
  const stop=()=>{interrupted=true;terminateTree(child);};
  process.once('SIGINT',stop);process.once('SIGTERM',stop);
  const resourceTimer=setInterval(()=>{
    if(process.platform!=='linux')return;
    const last=sampler.samples.at(-1),available=Number(readFileSync('/proc/meminfo','utf8').match(/MemAvailable:\s+(\d+)/)[1])*1024;
    if(last?.rssBytes>(options.memoryMaxMiB??4096)*1024**2||available<(options.memoryReserveMiB??12288)*1024**2){resourceStop=true;terminateTree(child);}
  },500);
  // Capture before VS Code's test runner closes the window. The host writes a
  // completion marker then waits briefly for this observer's acknowledgement.
  const renderTimer=setInterval(()=>{
    if(!probing&&existsSync(join(config.dir,'renderer-probe.json'))) {
      probing=true;
      probeTask=(async()=>{
        let client;
        try {client=await renderer.connect(debugPort);probe=await renderer.inputProbe(client);}
        catch(error){probe={error:error.message};}
        finally{client?.close();}
      })();
    }
    if(rendering||!existsSync(config.result))return;rendering=true;
    captureTask=(async()=>{
    try {
      rendererClient=await renderer.connect(debugPort);
      const evidence=JSON.parse(readFileSync(config.result,'utf8'));
      const visualBaseline=config.trial===0&&config.workers===1&&config.cache==='none';
      rendererCapture=await renderer.capture(rendererClient,config.dir,['broken','timeout'].includes(evidence.status)||visualBaseline);
    } catch(error) {rendererCapture={captured:false,error:error.message};}
    finally {rendererClient?.close();writeFileSync(join(config.dir,'renderer-done'),'done');}
    })();
  },100);
  let deadlineTask;
  const timer=setTimeout(()=>{
    timedOut=true;
    deadlineTask=(async()=>{
      let client;
      try{client=await renderer.connect(debugPort);rendererCapture=await renderer.capture(client,config.dir,true);}
      catch(error){rendererCapture={captured:false,error:error.message};}
      finally{client?.close();terminateTree(child);}
    })();
  },options.timeoutMs);
  let exitCode,error;
  await new Promise(resolvePromise=>{child.on('error',e=>{error=e.message;resolvePromise();});child.on('close',code=>{exitCode=code;resolvePromise();});});
  clearTimeout(timer);clearInterval(renderTimer);clearInterval(resourceTimer);
  if(probeTask)await probeTask;
  if(deadlineTask)await deadlineTask;
  if(captureTask)await captureTask;
  process.removeListener('SIGINT',stop);process.removeListener('SIGTERM',stop);closeSync(logfile);
  const resources=sampler.stop();
  const survivors=sampler.survivors();
  for(const owned of survivors)if(sampler.survivors().some(p=>p.pid===owned.pid&&p.start===owned.start))terminateTree({pid:owned.pid});
  const cleanupStart=performance.now();
  while(sampler.survivors().length&&performance.now()-cleanupStart<1000)await new Promise(resolve=>setTimeout(resolve,20));
  resources.cleanup={terminatedOwnedSurvivors:survivors,remaining:sampler.survivors()};
  writeFileSync(join(config.dir,'resources.json'),JSON.stringify(resources));
  // A successful exit alone is insufficient; this path belongs to this launch.
  let result;try{result=JSON.parse(readFileSync(config.result,'utf8'));}catch(e){error=error||'No fresh extension-host report: '+e.message;}
  if(probe?.started&&existsSync(join(config.dir,'renderer-probe-end.json'))) {
    const begin=JSON.parse(readFileSync(join(config.dir,'renderer-probe.json'),'utf8')).started;
    const end=JSON.parse(readFileSync(join(config.dir,'renderer-probe-end.json'),'utf8')).finished;
    probe.observedDuringVerification=probe.started>=begin&&probe.finished<=end;
    if(result?.metrics&&probe.observedDuringVerification&&probe.focusedEditor)result.metrics.rendererKeyRoundTripMs=probe.roundTripMs;
  }
  if(result&&(result.runId!==config.runId||result.target!==config.target||result.schemaVersion!==1||!Array.isArray(result.scenarios)||!result.checks?.includes('initial-verification'))) {
    error='Host evidence is stale, incomplete or belongs to another launch';result=undefined;
  }
  if(resources.cleanup.remaining.length)error='Owned verifier processes survived cleanup; subsequent trials must not run';
  const run={target:config.target,workers:config.workers,cache:config.cache,suite:options.suite||'full',trial:config.trial,warmup:config.warmup,
    status:interrupted?'interrupted':resourceStop?'resource-stop':timedOut||result?.status==='timeout'?'timeout':
      !error&&exitCode===0&&['passed','passed-with-gaps'].includes(result?.status)?result.status:'broken',exitCode,error,
    wallMs:performance.now()-start,result,resources:{...resources,samples:undefined},artifacts:config.dir,
    renderer:{...(rendererCapture||{captured:false,reason:'Host did not reach renderer capture'}),inputProbe:probe||{status:'unexamined'}},
    protocol:config.target==='local'?{status:'missing',transport:'CLI JSON',reason:'No LSP endpoint in this extension'}:protocol(options.trace==='off'?null:config.trace),
    applied:config.target==='local'?{workers:null,cache:null,reason:'Local extension has no worker or verification cache configuration'}:{workers:config.workers,cache:config.cache}};
  if(result?.initialCompletedSinceHostMs!==undefined)run.result.metrics.processLaunchThroughVerificationMs=result.startedWallTime-launchedWallTime+result.initialCompletedSinceHostMs;
  if(result?.metrics?.activationMs!==undefined)run.result.metrics.processLaunchThroughActivationMs=result.startedWallTime-launchedWallTime+result.metrics.activationMs;
  const logs=join(portable,'user-data/logs');
  if(existsSync(logs))cpSync(logs,join(config.dir,'editor-logs'),{recursive:true});
  rmSync(editorState,{recursive:true,force:true});
  return run;
}
async function main(args=process.argv.slice(2)) {
  const options=parse(args);
  if(options.help) {process.stdout.write('node vscode/parity/run.cjs --code PATH --dafny PATH --dafny-extension DIR --dotnet PATH [--output DIR] [--trials 5] [--warmups 1] [--workers 1,2,4] [--cache none,basic] [--targets dafny,local]\n');return;}
  for(const key of ['code',...(options.targets.includes('dafny')?['dafny','dafnyExtension','dotnet']:[])])if(!options[key]||!existsSync(options[key]))throw new Error('Missing executable/source --'+key);
  const output=resolve(options.output||join(repo,'.cache/editor-parity',new Date().toISOString().replaceAll(':','-')));
  if(existsSync(join(output,'report.json')))throw new Error('Output already contains a report; choose a new directory');
  mkdirSync(output,{recursive:true});
  // A single lock serializes competing harness instances across output paths.
  const lock=join(tmpdir(),'solidity-lean-editor-parity.lock');
  try{mkdirSync(lock);}catch{throw new Error('Another parity harness owns '+lock+'; inspect it before removing a stale lock');}
  writeFileSync(join(lock,'owner.json'),JSON.stringify({pid:process.pid,output}));
  try {
  const runs=[];
  const report={schemaVersion:1,started:new Date().toISOString(),status:'running',options,environment:{node:process.version,os:release(),platform:process.platform,
    cpu:cpus()[0]?.model,logicalCpus:cpus().length,memoryBytes:totalmem(),localCommit:git(repo),dafnyExtensionCommit:options.dafnyExtension?git(options.dafnyExtension):null,
    vscodeVersion:existsSync(join(dirname(resolve(options.code)),'resources/app/package.json'))?JSON.parse(readFileSync(join(dirname(resolve(options.code)),'resources/app/package.json'),'utf8')).version:null,
    dafnyVersion:options.dafny?spawnSync(resolve(options.dafny),['--version'],{encoding:'utf8',timeout:10000}).stdout?.trim():null,
    dotnetVersion:options.dotnet?spawnSync(resolve(options.dotnet),['--list-runtimes'],{encoding:'utf8',timeout:10000}).stdout?.trim():null,
    leanVersion:spawnSync('lean',['--version'],{encoding:'utf8',timeout:10000}).stdout?.trim()||null,
    cpuQuota:process.platform==='linux'&&existsSync('/sys/fs/cgroup/cpu.max')?readFileSync('/sys/fs/cgroup/cpu.max','utf8').trim():null,
    sourceFiles:Object.fromEntries(['vscode/src/extension.cjs','vscode/src/backend.cjs','vscode/parity/run.cjs','vscode/parity/host.cjs','vscode/parity/core.cjs','vscode/parity/observe.cjs','vscode/parity/renderer.cjs','vscode/parity/workloads.cjs'].map(path=>[path,createHash('sha256').update(readFileSync(join(repo,path))).digest('hex')])),
    memoryLimit:process.platform==='linux'&&existsSync('/sys/fs/cgroup/memory.max')?readFileSync('/sys/fs/cgroup/memory.max','utf8').trim():null},runs,summary:[],comparisons:[],
    limitations:['Equivalent constant-return obligations cover a shared semantic fragment, not general theorem-prover equivalence.',
      'No OS page-cache eviction is attempted. Process-cold and live-server warm timings are separate.',
      'Extension-host API and timer observations do not certify DOM rendering or renderer responsiveness.',
      'Solver time/resource limits differ in meaning between Z3 and kernel-checked Lean; total client deadlines are shared.',
      'Frontend, VC generation and solver phases remain unmeasured unless supplied by native notifications.',
      'Dafny protocol recording adds synchronous disk writes in the extension host; use --trace off for an observer-overhead control.',
      'Missing editor capabilities and incomplete scenarios prevent a claim of full parity.']};
  const inventory=JSON.parse(readFileSync(join(repo,'docs/dafny-editor-features.json'),'utf8'));
  const save=()=>{
    report.summary=summarize(runs);report.parallelScaling=scaling(report.summary);
    report.featureParity=inventory.features.map(feature=>{
      const evidence=runs.filter(r=>!r.warmup).flatMap(run=>(run.result?.scenarios||[]).filter(s=>feature.assessment.scenarioIds.includes(s.id)).map(s=>({target:run.target,scenario:s.id,status:s.status,artifact:join(run.artifacts,'result.json')})));
      const broken=evidence.some(e=>['broken','timeout'].includes(e.status));
      return {id:feature.id,status:broken?'broken':feature.assessment.status,sourceAssessment:feature.assessment.status,
        runtimeAssessment:broken?'broken':evidence.length?'observed-related-scenarios':'unexamined',reason:feature.assessment.reason,evidence};
    });
    writeFileSync(join(output,'report.json'),JSON.stringify(report,null,2));writeFileSync(join(output,'summary.md'),shortSummary(report));
  };
  try {
    for(const workers of options.workers) for(const cache of options.cache) for(let trial=-options.warmups;trial<options.trials;trial++) for(const target of trial%2===0?options.targets:[...options.targets].reverse()) {
      const dir=join(output,`${target}-w${workers}-${cache}-${trial<0?'warmup'+(-trial):trial}`);
      mkdirSync(dir,{recursive:true});
      const config={dir,target,workers,cache,trial,warmup:trial<0,workspace:join(dir,'workspace'),result:join(dir,'result.json'),events:join(dir,'events.jsonl'),trace:join(dir,'lsp.jsonl')};
      process.stdout.write(`Running ${target}, workers=${workers}, cache=${cache}, trial=${trial}\n`);
      runs.push(await launch(config,options));save();
      if(['interrupted','resource-stop'].includes(runs.at(-1).status))throw new Error('Run stopped: '+runs.at(-1).status);
      if(runs.at(-1).resources.cleanup.remaining.length)throw new Error(runs.at(-1).error);
    }
    for(const left of runs.filter(r=>r.target==='dafny'&&!r.warmup)) {
      const right=runs.find(r=>r.target==='local'&&r.trial===left.trial&&r.workers===left.workers&&r.cache===left.cache);
      if(!right)continue;
      for(const a of left.result?.scenarios||[]) {
        const b=right.result?.scenarios.find(s=>s.id===a.id);
        const observable=s=>({status:s?.status,observation:s?.observation??null});
        report.comparisons.push({scenario:a.id,workers:left.workers,cache:left.cache,trial:left.trial,
          differences:differences(normalize(observable(a),[left.artifacts]),normalize(observable(b),[right.artifacts]))});
      }
    }
    report.status=runs.every(r=>['passed','passed-with-gaps'].includes(r.status))?'completed-with-gaps':'incomplete';
  } catch(error) {report.status='incomplete';report.error=error.stack;throw error;}
  finally {report.finished=new Date().toISOString();save();}
  process.stdout.write(join(output,'summary.md')+'\n');
  if(report.status==='incomplete')process.exitCode=1;
  return report;
  } finally {rmSync(lock,{recursive:true,force:true});}
}
module.exports={parse,main,launch,shortSummary};
if(require.main===module)main().catch(error=>{process.stderr.write(error.stack+'\n');process.exitCode=1;});
