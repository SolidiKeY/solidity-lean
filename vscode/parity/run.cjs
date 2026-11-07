#!/usr/bin/env node
'use strict';
const {spawn,spawnSync} = require('node:child_process');
const {mkdirSync,mkdtempSync,readFileSync,writeFileSync,existsSync,rmSync,openSync,closeSync,cpSync,appendFileSync} = require('node:fs');
const {resolve,join,dirname} = require('node:path');
const {tmpdir,cpus,totalmem,release} = require('node:os');
const {performance} = require('node:perf_hooks');
const {randomUUID,createHash} = require('node:crypto');
const {ProcessSampler,summarize,differences,normalize,scaling,protocol,hostEvidenceErrors} = require('./core.cjs');
const {terminateTree} = require('../src/backend.cjs');
const renderer=require('./renderer.cjs');
const {servePhases,atomicJson}=require('./phase-capture.cjs');
const repo=resolve(__dirname,'../..');

function retireSampledSurvivors(sampler){
 const survivors=sampler.survivors(),refused=[],terminated=[];
 for(const owned of survivors)if(sampler.survivors().some(p=>p.pid===owned.pid&&p.start===owned.start))try{terminateTree({pid:owned.pid,processBirth:owned.start});terminated.push(owned);}catch(error){refused.push({pid:owned.pid,birth:owned.start,error:error.message});}
 return {survivors,refused,terminated};
}

function assertRetirementComplete(run){
 const cleanup=run?.resources?.cleanup;if(!Array.isArray(cleanup?.remaining)||!Array.isArray(cleanup.identityRefusals))throw Error('Missing cleanup ownership evidence');
 if(cleanup.remaining.length||cleanup.identityRefusals.length)throw new Error(run.error||'Owned process retirement incomplete');
}

function readKeybindingRequest(file,seen){
 let text;
 try{text=readFileSync(file,'utf8');const request=JSON.parse(text);if(!request||typeof request.runId!=='string'||typeof request.requestId!=='string'||!request.requestId)throw Error('Invalid keybinding request identity');if(seen?.has(request.requestId))return{ignored:true};seen?.add(request.requestId);return{request};}
 catch(error){return{error:{message:error.message,code:error.code||'INVALID_REQUEST',sha256:text===undefined?null:createHash('sha256').update(text).digest('hex')}};}
}

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
  if(options.targets.includes('local')&&options.workers.some(w=>w>4))throw new Error('Local workers must be between 1 and 4');
  if(options.cache.some(t=>!['none','basic','advanced'].includes(t))) throw new Error('Invalid cache');
  for(const key of ['workers','targets','cache'])if(new Set(options[key]).size!==options[key].length)throw new Error('Duplicate '+key);
  if(options.obligations>1000||options.trials>100||options.warmups>10)throw new Error('Excessive benchmark dimensions');
  if(!['on','off'].includes(options.trace))throw new Error('Invalid trace');
  if(!['full','benchmark','visual','commands','custom-commands','custom-default-commands','custom-import-actions','compiler-output','dafny-compiler-output','dafny-command-output','output-lifecycle','trace-unavailable','trace-visibility','trace-light-show','proof-help','proof-hover'].includes(options.suite))throw new Error('Invalid suite');
  if(options.suite==='trace-unavailable'&&options.trace==='off')throw Error('Unavailable trace absence assertions require recorded protocol');
  if(options.suite==='trace-unavailable'&&(options.targets.length!==1||options.targets[0]!=='local'))throw Error('Unavailable trace suite requires --targets local');
  if(['trace-visibility','trace-light-show'].includes(options.suite)&&(options.targets.length!==1||options.targets[0]!=='dafny'))throw Error('Native trace visibility suite requires --targets dafny; local producer remains absent');
  if(['proof-help','proof-hover'].includes(options.suite)&&(options.targets.length!==1||options.targets[0]!=='local'||options.workers.some(w=>w!==1)||options.obligations!==1||options.trace!=='on'))throw Error('Certified proof-help observation requires one local worker, one obligation and protocol recording');
  if(['dafny-compiler-output','dafny-command-output'].includes(options.suite)&&(options.targets.length!==1||options.targets[0]!=='dafny'))throw Error('Upstream output observation requires --targets dafny');
  if(options.suite==='compiler-output'&&(options.targets.length!==1||options.targets[0]!=='local'))throw Error('Compiler-output observation requires --targets local; paired upstream configuration remains pending');
  if(options.suite==='commands'&&(options.targets.length!==1||options.targets[0]!=='local'))throw new Error('Concrete command suite requires --targets local; no Dafny command equivalence is claimed');
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
  lines.push('','Local workers bound concurrent functions and files (1–4). Assertions within one function remain serial. Local exact-snapshot caching is always enabled; Dafny cache policy names do not select equivalent local policies.',
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
  config={...config,suite:options.suite||'full',runId:randomUUID()};
  mkdirSync(config.dir,{recursive:true});mkdirSync(config.workspace,{recursive:true});config.filesystemCapability=require('./filesystem.cjs').recursiveCapability(config.dir);
  const cache={'none':'No caching',basic:'Basic caching',advanced:'Advanced caching'}[config.cache];
  const settings= config.target==='dafny' ? {'dafny.version':'custom','dafny.cliPath':resolve(options.dafny),'dafny.dotnetExecutablePath':resolve(options.dotnet),
    'dafny.verificationVirtualCores':config.workers,'dafny.verificationCachingPolicy':cache,'dafny.verificationTimeLimit':20,
    'dafny.automaticVerification':'onchange','dafny.displayGutterStatus':true,'dafny.markGhostStatements':true} : {
    'solidityLean.backendPath':repo,'solidityLean.nodePath':process.execPath,'solidityLean.timeoutMs':options.operationTimeoutMs};
  if(config.target==='dafny'&&process.platform==='linux'){const sdk=dirname(resolve(options.dotnet));settings['terminal.integrated.env.linux']={PATH:sdk+':${env:PATH}',DOTNET_ROOT:sdk};}
  settings['files.autoSave']='off';settings['telemetry.telemetryLevel']='off';settings['update.mode']='none';
  settings['git.enabled']=false;settings['workbench.secondarySideBar.defaultVisibility']='hidden';
  if(['proof-help','proof-hover'].includes(options.suite))settings['solidityLean.counterexamples']=true;
  if(config.target==='local'){settings['solidityLean.workers']=config.workers;settings['solidityLean.automaticVerification']=options.suite==='visual'?'onchange':'never';}
  mkdirSync(join(config.workspace,'.vscode'),{recursive:true});
  writeFileSync(join(config.workspace,'.vscode/settings.json'),JSON.stringify(settings));
  const runtimeEnvironment=Object.fromEntries(['PATH','SOLKEY_ROOT','LEAN_NUM_THREADS','XDG_CACHE_HOME'].filter(k=>process.env[k]!==undefined).map(k=>[k,process.env[k]]));
  if(['compiler-output','dafny-compiler-output','dafny-command-output'].includes(options.suite)){config.foreignWorkspace=join(config.dir,'unrelated-resource');mkdirSync(join(config.foreignWorkspace,'.vscode'),{recursive:true});writeFileSync(join(config.foreignWorkspace,'.vscode/settings.json'),'{}');config.workspaceFile=join(config.dir,'output.code-workspace');writeFileSync(config.workspaceFile,JSON.stringify({folders:[{name:'Primary',path:config.workspace},{name:'Unrelated',path:config.foreignWorkspace}],...(['dafny-compiler-output','dafny-command-output'].includes(options.suite)?{settings}: {})}));}
  const hostConfig={...config,backendPath:config.target==='local'?repo:undefined,dafnyExecutable:config.target==='dafny'?resolve(options.dafny):undefined,dotnetExecutable:config.target==='dafny'?resolve(options.dotnet):undefined,dotnetVersion:config.target==='dafny'?spawnSync(resolve(options.dotnet),['--version'],{encoding:'utf8',timeout:5000}).stdout?.trim():undefined,suite:options.suite||'full',runtimeEnvironment,recordProtocol:options.trace!=='off',obligations:options.obligations,operationTimeoutMs:options.operationTimeoutMs};
  const configPath=join(config.dir,'config.json');writeFileSync(configPath,JSON.stringify(hostConfig));
  const extension=config.target==='local'?resolve(repo,'vscode'):resolve(options.dafnyExtension);
  const resource=require('./resource-state.cjs'),admission=process.platform==='linux'?resource.resourceState():null;
  writeFileSync(join(config.dir,'resource-admission.json'),JSON.stringify({snapshot:admission,options:{memoryMaxMiB:options.memoryMaxMiB??4096,memoryReserveMiB:options.memoryReserveMiB??12288},scope:'Native process-tree RSS sampling, no aggregate cgroup'}));
  if(admission&&!resource.resourcesAllowed(admission,options))throw Error('Native editor resource admission denied before launch');
  const logfile=openSync(join(config.dir,'editor.log'),'w');
  const debugPort=await renderer.availablePort();
  // VS Code's Unix socket path is limited to 107 bytes. Artifact paths may be
  // arbitrarily deep, so editor state must live under a short temporary root.
  const editorState=mkdtempSync(join(tmpdir(),'slp-'));
  const portable=join(editorState,'p');mkdirSync(portable,{recursive:true});writeFileSync(join(portable,'argv.json'),'{}');
  const start=performance.now(),launchedWallTime=Date.now();
  const child=spawn(resolve(options.code),[config.workspaceFile||config.workspace,'--disable-gpu','--disable-workspace-trust','--skip-welcome','--skip-release-notes','--no-sandbox',
    '--disable-updates','--remote-debugging-port='+debugPort,'--user-data-dir',join(editorState,'u'),'--extensions-dir',join(editorState,'e'),
    '--extensionDevelopmentPath='+extension,'--extensionTestsPath='+join(__dirname,'host.cjs')],{
    cwd:repo,detached:process.platform!=='win32',stdio:['ignore',logfile,logfile],
    env:{...process.env,VSCODE_CLI:'1',VSCODE_PORTABLE:portable,PARITY_HOST_CONFIG:configPath}});
  const sampler=new ProcessSampler(child.pid);
  let timedOut=false,interrupted=false,resourceStop=false,resourceStopDetails,rendererClient,rendererCapture,rendering=false,probe,probing=false,probeTask,captureTask;
  const stop=()=>{interrupted=true;terminateTree(child);};
  process.once('SIGINT',stop);process.once('SIGTERM',stop);
  const resourceTimer=setInterval(()=>{
    if(process.platform!=='linux')return;
    try{const last=sampler.samples.at(-1),state=resource.resourceState();
      if(!resource.resourcesAllowed(state,options,last?.rssBytes??0)){resourceStop=true;resourceStopDetails={...state,rssBytes:last?.rssBytes??0};terminateTree(child);}
    }catch(error){resourceStop=true;resourceStopDetails={error:error.message};terminateTree(child);}
  },500);
  // Capture before VS Code's test runner closes the window. The host writes a
  // completion marker then waits briefly for this observer's acknowledgement.
  const seenPhases=new Set();let phaseTask,phaseBusy=false;
  const seenKeybindingRequests=new Set();let keybindingTask,keybindingBusy=false,lastKeybindingReadError;
  const renderTimer=setInterval(()=>{
    if(['commands','custom-commands','custom-default-commands','custom-import-actions','compiler-output','dafny-compiler-output','dafny-command-output'].includes(options.suite)&&!keybindingBusy&&existsSync(join(config.dir,'keybinding-request.json'))){
      const read=readKeybindingRequest(join(config.dir,'keybinding-request.json'),seenKeybindingRequests);
      if(read.error){const signature=JSON.stringify(read.error);if(signature!==lastKeybindingReadError){appendFileSync(join(config.dir,'keybinding-read-errors.jsonl'),JSON.stringify({at:Date.now(),...read.error})+'\n');lastKeybindingReadError=signature;}}
      const request=read.request;if(request)lastKeybindingReadError=undefined;
      if(request){
        keybindingBusy=true;
        keybindingTask=(async()=>{let client;try{
          if(request.runId!==config.runId)throw Error('Foreign keybinding request');
          client=await renderer.connect(debugPort);
          if(['compiler-output','dafny-compiler-output','dafny-command-output'].includes(options.suite)&&!/^[a-z]+(?:-[a-z]+)*$/.test(request.caseId||''))throw Error('Invalid configuration action identity');
          const base=['compiler-output','dafny-compiler-output','dafny-command-output'].includes(options.suite)?join(config.dir,'configuration-actions',request.caseId):options.suite==='custom-import-actions'?join(config.dir,request.refusal==='syntax'?'invalid-json-action':request.refusal==='options'?'unsupported-option-action':request.cancel?'cancel-action':'build-action'):config.dir;
          mkdirSync(base,{recursive:true});const menuDirectory=join(base,'context-menu');mkdirSync(menuDirectory,{recursive:true});
          const contextMenu=await renderer.contextSubmenu(client,menuDirectory,config.target==='dafny'?{label:'Dafny',expected:'Build with Custom Arguments'}:undefined);
          const promptDirectory=join(base,'custom-prompt');mkdirSync(promptDirectory,{recursive:true});
          const observation={...await renderer.buildKeybinding(client,{operation:request.operation||'build',custom:options.suite!=='commands'&&request.ordinary!==true,onPrompt:request.hold?async prompt=>{atomicJson(join(config.dir,'keybinding-held.json'),{runId:config.runId,requestId:request.requestId,heldAt:Date.now(),prompt});while(Date.now()<prompt.deadline){const file=join(config.dir,'keybinding-resume.json');if(existsSync(file)){const resume=JSON.parse(readFileSync(file,'utf8'));if(resume.runId===config.runId&&resume.requestId===request.requestId)return;}await new Promise(resolve=>setTimeout(resolve,20));}throw Error('Pending F6 configuration handshake exhausted original prompt deadline');}:undefined,input:request.customInput,cancel:request.cancel===true,dismissOnSubmit:request.refusal==='syntax'||request.refusal==='options',directory:promptDirectory}),contextMenu};
          atomicJson(join(config.dir,'keybinding-reply.json'),{runId:config.runId,requestId:request.requestId,observation});
        }catch(error){atomicJson(join(config.dir,'keybinding-reply.json'),{runId:config.runId,requestId:request.requestId,error:error.message});}finally{client?.close();keybindingBusy=false;}})();
      }
    }
    if((['visual','proof-help','proof-hover','output-lifecycle','trace-unavailable','compiler-output','dafny-compiler-output','dafny-command-output'].includes(options.suite)||['custom-default-commands','trace-visibility','trace-light-show'].includes(options.suite)&&config.target==='dafny')&&!phaseBusy){
      phaseBusy=true;
      phaseTask=servePhases(config.dir,config.runId,async (directory,request)=>{
        const client=await renderer.connect(debugPort);try{if(request.phase.startsWith('dafny-command-'))return await renderer.captureCompilerConfiguration(client,directory,request.metadata);if(request.phase.startsWith('compiler-output-')||request.phase.startsWith('dafny-output-'))return await renderer.captureCompilerConfiguration(client,directory,request.metadata);if(request.phase==='output-channel')return await renderer.captureOutput(client,directory,request.metadata);if(request.phase.startsWith('proof-help-'))return await renderer.captureProofHelp(client,directory,request.metadata);if(request.phase.startsWith('trace-'))return await renderer.captureTrace(client,directory,request.metadata);const rendered=await renderer.capture(client,directory,true);if(options.suite==='custom-default-commands'){const menu=join(directory,'menu');mkdirSync(menu,{recursive:true});rendered.contextMenu=await renderer.contextSubmenu(client,menu,{label:'Dafny',expected:'Build with Custom Arguments'});}return rendered;}finally{client.close();}
      },seenPhases).catch(error=>{rendererCapture={captured:false,error:error.message};}).finally(()=>{phaseBusy=false;});
    }
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
  if(phaseTask)await phaseTask;
  if(keybindingTask)await keybindingTask;
  if(probeTask)await probeTask;
  if(deadlineTask)await deadlineTask;
  if(captureTask)await captureTask;
  process.removeListener('SIGINT',stop);process.removeListener('SIGTERM',stop);closeSync(logfile);
  const resources=sampler.stop();
  const cleanup=retireSampledSurvivors(sampler);
  const cleanupStart=performance.now();
  while(sampler.survivors().length&&performance.now()-cleanupStart<1000)await new Promise(resolve=>setTimeout(resolve,20));
  resources.cleanup={observedOwnedSurvivors:cleanup.survivors,terminatedOwnedSurvivors:cleanup.terminated,identityRefusals:cleanup.refused,remaining:sampler.survivors()};
  writeFileSync(join(config.dir,'resources.json'),JSON.stringify(resources));
  // A successful exit alone is insufficient; this path belongs to this launch.
  let result;try{result=JSON.parse(readFileSync(config.result,'utf8'));}catch(e){error=error||'No fresh extension-host report: '+e.message;}
  if(probe?.started&&existsSync(join(config.dir,'renderer-probe-end.json'))) {
    const begin=JSON.parse(readFileSync(join(config.dir,'renderer-probe.json'),'utf8')).started;
    const end=JSON.parse(readFileSync(join(config.dir,'renderer-probe-end.json'),'utf8')).finished;
    probe.observedDuringVerification=probe.started>=begin&&probe.finished<=end;
    if(result?.metrics&&probe.observedDuringVerification&&probe.focusedEditor)result.metrics.rendererKeyRoundTripMs=probe.roundTripMs;
  }
  let rejectedResult,validationErrors;
  if(result){const checked=require('./core.cjs').validateHostResult(result,config);if(checked.error){error=checked.error;rejectedResult=checked.rejectedResult;validationErrors=checked.validationErrors;result=undefined;}}
  if(cleanup.refused.length)error='Owned process identity changed during cleanup; no subsequent trial admitted';
  if(resources.cleanup.remaining.length)error='Owned verifier processes survived cleanup; subsequent trials must not run';
  writeFileSync(join(config.dir,'resource-terminal.json'),JSON.stringify({resourceStop,resourceStopDetails:resourceStopDetails??null}));
  const run={target:config.target,workers:config.workers,cache:config.cache,suite:options.suite||'full',trial:config.trial,warmup:config.warmup,
    status:interrupted?'interrupted':resourceStop?'resource-stop':timedOut||result?.status==='timeout'?'timeout':
      !error&&exitCode===0&&['passed','passed-with-gaps'].includes(result?.status)?result.status:'broken',exitCode,error,
    wallMs:performance.now()-start,result,rejectedResult,validationErrors,resources:{...resources,samples:undefined},artifacts:config.dir,
    renderer:{...(rendererCapture||{captured:false,reason:'Host did not reach renderer capture'}),inputProbe:probe||{status:'unexamined'}},
    protocol:protocol(options.trace==='off'?null:config.trace),
    applied:config.target==='local'?{workers:config.workers,cache:'exact snapshot and persistent Lean document',reason:'The local cache does not implement Dafny caching-policy levels'}:{workers:config.workers,cache:config.cache}};
  if(result?.initialCompletedSinceHostMs!==undefined)run.result.metrics.processLaunchThroughVerificationMs=result.startedWallTime-launchedWallTime+result.initialCompletedSinceHostMs;
  if(result?.metrics?.activationMs!==undefined)run.result.metrics.processLaunchThroughActivationMs=result.startedWallTime-launchedWallTime+result.metrics.activationMs;
  const logs=join(portable,'user-data/logs');
  if(existsSync(logs))cpSync(logs,join(config.dir,'editor-logs'),{recursive:true});
  rmSync(editorState,{recursive:true,force:true});
  return run;
}
async function main(args=process.argv.slice(2)) {
  const options=parse(args);
  if(options.help) {process.stdout.write('node vscode/parity/run.cjs --code PATH --dafny PATH --dafny-extension DIR --dotnet PATH [--output DIR] [--trials 5] [--warmups 1] [--workers 1,2,4] [--cache none,basic] [--targets dafny,local] [--suite full|commands|custom-commands|custom-default-commands|custom-import-actions|compiler-output|dafny-compiler-output|dafny-command-output|visual|proof-help|proof-hover]\n');return;}
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
    sourceFiles:Object.fromEntries(['vscode/src/extension.cjs','vscode/src/backend.cjs','vscode/src/rpc.cjs','vscode/src/lsp-client.cjs','vscode/src/lsp-server.cjs','vscode/src/lsp-worker.cjs','vscode/src/lean-session.cjs','vscode/src/worker-pool.cjs','vscode/src/language-services.cjs','vscode/src/editor-services.cjs','vscode/src/project.cjs','vscode/src/solidity-text.cjs','scripts/source-locations.mjs','scripts/test-solidity.mjs','scripts/solc-ast.mjs','vscode/parity/run.cjs','vscode/parity/host.cjs','vscode/parity/core.cjs','vscode/parity/observe.cjs','vscode/parity/renderer.cjs','vscode/parity/workloads.cjs'].map(path=>[path,createHash('sha256').update(readFileSync(join(repo,path))).digest('hex')])),
    memoryLimit:process.platform==='linux'&&existsSync('/sys/fs/cgroup/memory.max')?readFileSync('/sys/fs/cgroup/memory.max','utf8').trim():null},runs,summary:[],comparisons:[],
    limitations:['Equivalent constant-return obligations cover a shared semantic fragment, not general theorem-prover equivalence.',
      'No OS page-cache eviction is attempted. Process-cold and live-server warm timings are separate.',
      'Extension-host API and timer observations do not certify DOM rendering or renderer responsiveness.',
      'Solver time/resource limits differ in meaning between Z3 and kernel-checked Lean; total client deadlines are shared.',
      'Frontend, VC generation and solver phases remain unmeasured unless supplied by native notifications.',
      'Dafny protocol recording adds synchronous disk writes in the extension host; use --trace off for an observer-overhead control.',
      'Missing editor capabilities and incomplete scenarios prevent a claim of full parity.']};
  const inventory=require('./inventory.cjs').loadInventory();
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
      assertRetirementComplete(runs.at(-1));
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
module.exports={readKeybindingRequest,parse,main,launch,shortSummary,retireSampledSurvivors,assertRetirementComplete};
if(require.main===module)main().catch(error=>{process.stderr.write(error.stack+'\n');process.exitCode=1;});
