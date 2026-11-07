'use strict';
const {EventEmitter} = require('node:events');
const {readdirSync, readFileSync} = require('node:fs');
const {performance} = require('node:perf_hooks');
const {spawnSync}=require('node:child_process');

/** Byte-oriented framing: UTF-8 characters may straddle arbitrary pipe chunks. */
class LspFrames extends EventEmitter {
  constructor(limit = 32 * 1024 * 1024) { super(); this.buffer = Buffer.alloc(0); this.limit = limit; }
  push(chunk) {
    this.buffer = Buffer.concat([this.buffer, chunk]);
    while (this.buffer.length) {
      const end = this.buffer.indexOf('\r\n\r\n');
      if (end < 0) { if (this.buffer.length > 8192) throw new Error('Oversize LSP header'); return; }
      const lengths = [...this.buffer.subarray(0, end).toString('ascii').matchAll(/^Content-Length:\s*(\d+)\s*$/gim)];
      if (lengths.length !== 1) throw new Error('Invalid LSP Content-Length');
      const length = Number(lengths[0][1]);
      if (!Number.isSafeInteger(length) || length > this.limit) throw new Error('Oversize LSP body');
      if (this.buffer.length < end + 4 + length) return;
      const body = this.buffer.subarray(end + 4, end + 4 + length);
      this.buffer = this.buffer.subarray(end + 4 + length);
      this.emit('message', JSON.parse(body.toString('utf8')));
    }
  }
  end() { if (this.buffer.length) throw new Error('Truncated LSP frame'); }
}

function statistics(values) {
  const sorted = values.filter(Number.isFinite).sort((a, b) => a - b);
  if (!sorted.length) return {n:0, median:null, p95:null, min:null, max:null, standardDeviation:null};
  const quantile = p => sorted[Math.max(0, Math.ceil(p * sorted.length) - 1)];
  const mean = sorted.reduce((a,b) => a+b, 0) / sorted.length;
  const middle = Math.floor(sorted.length/2);
  return {n:sorted.length, median:sorted.length % 2 ? sorted[middle] : (sorted[middle-1]+sorted[middle])/2,
    p95:quantile(.95), min:sorted[0], max:sorted.at(-1),
    standardDeviation:Math.sqrt(sorted.reduce((s,v) => s + (v-mean)**2, 0)/sorted.length)};
}

/** Only explicit workspace roots are normalized. Preserve versions, status, order,
 * diagnostic severities, messages and source ranges; translations are separate. */
function normalize(value, roots = []) {
  if (typeof value === 'string') {
    for (const root of [...roots].filter(Boolean).sort((a,b) => b.length-a.length)) {
      value = value.split(root).join('<workspace>');
    }
    return value;
  }
  if (Array.isArray(value)) return value.map(v => normalize(v, roots));
  if (value && typeof value === 'object') return Object.fromEntries(Object.entries(value).map(([k,v]) => [k, normalize(v, roots)]));
  return value;
}

function differences(left, right, path = '$') {
  if (JSON.stringify(left) === JSON.stringify(right)) return [];
  if (!left || !right || typeof left !== 'object' || typeof right !== 'object' || Array.isArray(left) !== Array.isArray(right))
    return [{path, left:left ?? null, right:right ?? null}];
  return [...new Set([...Object.keys(left), ...Object.keys(right)])].flatMap(key => differences(left[key], right[key], `${path}.${key}`));
}

function procTable() {
  const table = new Map();
  for (const name of readdirSync('/proc')) {
    if (!/^\d+$/.test(name)) continue;
    try {
      const text = readFileSync(`/proc/${name}/stat`, 'utf8');
      const end = text.lastIndexOf(')');
      const fields = text.slice(end+2).trim().split(/\s+/);
      const cmd = readFileSync(`/proc/${name}/cmdline`, 'utf8').replaceAll('\0', ' ');
      table.set(Number(name), {pid:Number(name), ppid:Number(fields[1]), state:fields[0],name:text.slice(text.indexOf('(')+1,end),
        ticks:Number(fields[11])+Number(fields[12]), start:fields[19], rssBytes:Number(fields[21])*4096, cmd});
    } catch { /* Processes can exit between reads. */ }
  }
  return table;
}

/** Sampling is evidence of CPU overlap only when distinct processes accumulate
 * CPU ticks in the same interval. Sleeping children do not establish parallelism. */
class ProcessSampler {
  constructor(root, intervalMs = 100) {
    this.root = root; this.samples = []; this.seen = new Map(); this.previous = new Map();
    this.start = performance.now(); this.sample();
    this.ticksPerSecond=process.platform==='linux'?Number(spawnSync('getconf',['CLK_TCK'],{encoding:'utf8',timeout:1000}).stdout?.trim())||null:null;
    this.timer = setInterval(() => this.sample(), intervalMs); this.timer.unref();
  }
  sample() {
    if (process.platform !== 'linux') return;
    const table = procTable();
    if(this.rootStart===undefined)this.rootStart=table.get(this.root)?.start;
    const ids = new Set(table.get(this.root)?.start===this.rootStart?[this.root]:[]);
    // Retain known detached descendants, checking start time against PID reuse.
    for (const [pid, start] of this.seen) if (table.get(pid)?.start === start) ids.add(pid);
    let changed = true;
    while (changed) { changed = false; for (const row of table.values()) if (ids.has(row.ppid) && !ids.has(row.pid)) { ids.add(row.pid); changed = true; } }
    const rows = [...ids].map(pid => table.get(pid)).filter(Boolean);
    let activeCpuProcesses = 0, activeVerifierProcesses = 0, cpuTicks = 0;
    for (const row of rows) {
      this.seen.set(row.pid,row.start);
      const old = this.previous.get(row.pid);
      const delta = old?.start === row.start ? Math.max(0,row.ticks-old.ticks) : row.ticks;
      cpuTicks += delta;
      if (delta > 0) {
        activeCpuProcesses++;
        if (/^(z3(?:-|$)|lean$|dafny$|Dafny$)/.test(row.name)) activeVerifierProcesses++;
      }
      this.previous.set(row.pid,{start:row.start,ticks:row.ticks});
    }
    this.samples.push({ms:performance.now()-this.start,rssBytes:rows.reduce((s,r)=>s+r.rssBytes,0),cpuTicks,
      activeCpuProcesses,activeVerifierProcesses,processes:rows.map(({pid,ppid,name,ticks,rssBytes,start})=>({pid,ppid,name,ticks,rssBytes,start}))});
  }
  stop() {
    clearInterval(this.timer); this.sample();
    const cpuTicks=this.samples.reduce((s,r)=>s+r.cpuTicks,0),elapsedMs=performance.now()-this.start;
    return {platform:process.platform,ticksPerSecond:this.ticksPerSecond,cpuSeconds:this.ticksPerSecond?cpuTicks/this.ticksPerSecond:null,
      averageCpuCores:this.ticksPerSecond?cpuTicks/this.ticksPerSecond/(elapsedMs/1000):null,
      intervalMs:this.samples.length > 1 ? statistics(this.samples.slice(1).map((s,i)=>s.ms-this.samples[i].ms)).median : null,
      peakRssBytes:Math.max(0,...this.samples.map(s=>s.rssBytes)),cpuTicks:this.samples.reduce((s,r)=>s+r.cpuTicks,0),
      maxActiveVerifierProcesses:Math.max(0,...this.samples.slice(1).map(s=>s.activeVerifierProcesses)),samples:this.samples,
      limitations:['RSS sums can double-count shared pages; /proc sampling can miss short-lived children.',
        'CPU overlap in a sampling interval is evidence of work overlap, not proof of simultaneous instructions.']};
  }
  survivors() {
    if(process.platform!=='linux')return [];
    const table=procTable();
    return [...this.seen].flatMap(([pid,start])=>{
      const row=table.get(pid);return row?.start===start&&row.state!=='Z'?[{pid,start,name:row.name}]:[];
    });
  }
}

function summarize(runs) {
  const groups = new Map();
  for (const run of runs.filter(r=>!r.warmup)) {
    const key = JSON.stringify([run.target,run.workers,run.cache,run.suite]);
    if (!groups.has(key)) groups.set(key,[]);
    groups.get(key).push(run);
  }
  return [...groups.values()].map(rows => {
    const valid=rows.filter(r=>['passed','passed-with-gaps'].includes(r.status));
    const metrics = [...new Set(rows.flatMap(r=>Object.keys(r.result?.metrics || {})))];
    return {target:rows[0].target,workers:rows[0].workers,cache:rows[0].cache,suite:rows[0].suite,trials:rows.length,
      validTrials:valid.length,excludedTimingTrials:rows.length-valid.length,
      failures:rows.filter(r=>!['passed','passed-with-gaps'].includes(r.status)).length,
      capabilityGaps:rows.reduce((s,r)=>s+(r.result?.scenarios?.filter(t=>['missing','partial','unexamined'].includes(t.status)).length||0),0),
      timeoutRate:rows.filter(r=>r.status === 'timeout').length/rows.length,
      metrics:Object.fromEntries(metrics.map(key=>[key,statistics(valid.map(r=>r.result?.metrics[key]))])),
      peakRssBytes:statistics(rows.map(r=>r.resources?.peakRssBytes)),cpuTicks:statistics(rows.map(r=>r.resources?.cpuTicks)),
      cpuSeconds:statistics(rows.map(r=>r.resources?.cpuSeconds)),averageCpuCores:statistics(rows.map(r=>r.resources?.averageCpuCores)),
      activeVerifierProcesses:statistics(rows.map(r=>r.resources?.maxActiveVerifierProcesses))};
  });
}
function scaling(summary) {
  return summary.map(row=>{
    const baseline=summary.find(s=>s.target===row.target&&s.cache===row.cache&&s.suite===row.suite&&s.workers===1);
    const metric='initialVerificationMs';
    const latency=row.metrics[metric]?.median,base=baseline?.metrics[metric]?.median;
    return {target:row.target,cache:row.cache,workers:row.workers,baselineWorkers:1,
      speedup:base&&latency?base/latency:null,
      efficiency:base&&latency?base/latency/row.workers:null,
      scope:row.target==='dafny'?'End-to-end within-file declaration workload; frontend serialization and startup are included.':'End-to-end within-file function workload; listing and worker startup are included.'};
  });
}
function protocol(tracePath) {
  if(!tracePath)return {status:'unexamined',reason:'Tracing disabled'};
  let records;try{records=readFileSync(tracePath,'utf8').trim().split('\n').filter(Boolean).map(l=>JSON.parse(l));}
  catch(error){return {status:'unexamined',reason:error.message};}
  const methods={},errors=[],states=new Map(),queueMs=[],executionMs=[];
  let messages=0,framingErrors=0,statusErrors=0;const finalized=new Set();
  for(const [recordIndex,record] of records.entries()) {
    if(record.framingFinalized)finalized.add(record.direction);
    if(record.error){errors.push(record.error);framingErrors++;continue;}
    const message=record.message,method=message?.method;
    if(message)messages++;
    if(method)methods[record.direction+':'+method]=(methods[record.direction+':'+method]||0)+1;
    if(message?.error)errors.push(message.error);
    if(method==='dafny/textDocument/symbolStatus') {
      const params=message.params,position=p=>p&&Number.isInteger(p.line)&&p.line>=0&&Number.isInteger(p.character)&&p.character>=0;
      const range=r=>position(r?.start)&&position(r?.end)&&(r.start.line<r.end.line||r.start.line===r.end.line&&r.start.character<=r.end.character);
      const valid=record.direction==='server'&&params&&typeof params.uri==='string'&&(params.version===undefined||Number.isInteger(params.version))&&Array.isArray(params.namedVerifiables)&&Number.isFinite(record.time)&&params.namedVerifiables.every(symbol=>symbol&&[0,1,2,4,5].includes(symbol.status)&&range(symbol.nameRange));
      if(!valid){errors.push({kind:'malformed-symbol-status',recordIndex});statusErrors++;continue;}
      if(params.namedVerifiables.some(symbol=>{const previous=states.get(JSON.stringify([params.uri,params.version,symbol.nameRange]));return previous?.last!==undefined&&record.time<previous.last;})){errors.push({kind:'nonmonotonic-symbol-status',recordIndex});statusErrors++;continue;}
    }
    if(method==='dafny/textDocument/symbolStatus')for(const symbol of message.params.namedVerifiables) {
      const key=JSON.stringify([message.params.uri,message.params.version,symbol.nameRange]),previous=states.get(key)||{};
      if(symbol.status===1&&previous.queued===undefined)previous.queued=record.time;
      if(symbol.status===2&&previous.running===undefined){previous.running=record.time;if(previous.queued!==undefined)queueMs.push(record.time-previous.queued);}
      if(symbol.status>=4&&!previous.done){previous.done=true;if(previous.running!==undefined)executionMs.push(record.time-previous.running);}
      previous.last=record.time;states.set(key,previous);
    }
  }
  return {status:framingErrors||statusErrors?'broken':!messages?'unexamined':finalized.size===2?'observed':'partial',messageCount:messages,methods,errors,queueMs:statistics(queueMs),symbolExecutionMs:statistics(executionMs),
    framingFinalized:[...finalized],
    scope:'Native status notification intervals include transport and notification throttling; they do not isolate pure solver or VC time.'};
}
function outputLifecycleErrors(o,target){
 const errors=[],name=target==='local'?'Solidity Lean':'Dafny VSCode',command=target==='local'?'solidityLean.restartServer':'dafny.restartServer';
 if(!o||typeof o.uri!=='string'||!Number.isInteger(o.version)||!/^([a-f0-9]{64})$/.test(o.sourceHash||''))return ['missing output source identity'];
 const id=o.channel?.data?.channelId;
 if(o.channel?.kind!=='output.create'||o.channel?.data?.channel!==name||!Number.isInteger(id))errors.push('missing owned output channel');
 if(!Array.isArray(o.channels)||o.channels.length!==1||o.channels[0]?.kind!=='output.create'||o.channels[0]?.data?.channelId!==id||o.channels[0]?.data?.channel!==name)errors.push('output channel replaced or disposed');
 const text=again=>target==='local'?`Solidity Lean is ready${again?' again':''} for ${o.uri} (`:again?'Dafny is ready again.':'Dafny is ready';
 const owned=e=>e?.kind==='output'&&e.data?.channelId===id&&e.data.channel===name;
 if(!owned(o.startup)||!o.startup.data.text?.startsWith(text(false)))errors.push('missing owned initial readiness');
 const events=Array.isArray(o.events)?o.events:[],termination=events.findIndex(e=>owned(e)&&e.data.text?.startsWith('Terminating')),ready=events.findIndex(e=>owned(e)&&e.data.text?.startsWith(text(true)));
 if(termination<0||ready<=termination)errors.push('missing ordered owned restart output');
 const starts=events.filter(e=>e?.kind==='command.start'&&e.data?.id===command),ends=events.filter(e=>e?.kind==='command.end'&&e.data?.id===command);
 if(!Number.isFinite(o.channel?.ms)||!Number.isFinite(o.startup?.ms)||!Number.isFinite(starts[0]?.ms)||!(o.channel.ms<=o.startup.ms&&o.startup.ms<starts[0].ms))errors.push('missing initial output phase order');
 if(!(events.indexOf(starts[0])<termination&&termination<ready&&ready<events.indexOf(ends[0])))errors.push('output outside restart invocation');
 const source=s=>s&&s.uri===o.uri&&s.version===o.version&&s.textHash===o.sourceHash&&typeof s.session==='string'&&s.trusted===true&&!s.closed;
 if(starts.length!==1||ends.length!==1||starts[0]?.data.invocationId!==ends[0]?.data.invocationId||!source(starts[0]?.data.source)||!source(ends[0]?.data.source)||starts[0]?.data.source?.session!==ends[0]?.data.source?.session)errors.push('missing source-owned restart invocation');
 return errors;
}
function terminalSdkIdentity(output,executable,version){
 const lines=require('node:util').stripVTControlCharacters(output).split(/\r?\n/).map(line=>line.trim()).filter(Boolean),fs=require('node:fs');
 if(!version||lines[0]!==executable||lines[1]!==version)throw Error('Terminal SDK path/version differs from selected executable');
 const resolved=fs.realpathSync(lines[0]),selected=fs.realpathSync(executable),sha256=require('node:crypto').createHash('sha256').update(fs.readFileSync(resolved)).digest('hex');
 if(resolved!==selected)throw Error('Terminal SDK canonical executable differs from selected SDK');
 return{executable:resolved,sha256,version,lines};
}
// Preserve rejected observations for diagnosis; they never become accepted metrics.
function scenarioFailure(id,elapsedMs,error){return{id,status:error.code==='TIMEOUT'?'timeout':'broken',elapsedMs,error:error.stack||String(error),...(error.observation?{observation:error.observation}:{})};}
function validateHostResult(result,config){const validationErrors=hostEvidenceErrors(result,config);return validationErrors.length?{rejectedResult:result,validationErrors,error:'Host evidence is stale, incomplete or inconsistent: '+validationErrors.join('; ')}:{result};}
function hostEvidenceErrors(result,config) {
  const errors=[];
  if(result?.runId!==config.runId||result?.target!==config.target||result?.schemaVersion!==1)errors.push('stale or foreign identity');
  if(!Array.isArray(result?.scenarios)||!Array.isArray(result?.checks))return [...errors,'missing scenarios/checks'];
  const ids=result.scenarios.map(s=>s.id);
  if(ids.some(id=>typeof id!=='string')||new Set(ids).size!==ids.length)errors.push('invalid or duplicate scenario IDs');
  if(config.suite==='trace-unavailable'){errors.push(...require('./trace-presentation.cjs').unavailableErrors(result.scenarios.find(s=>s.id==='native-trace-unavailable')?.observation,config.runId));
  }else if(config.suite==='dafny-command-output'){const o=result.scenarios.find(s=>s.id==='native-dafny-command-output')?.observation;errors.push(...require('./dafny-command-output.cjs').errors(o,config.runId));
  }else if(config.suite==='dafny-compiler-output'){const o=result.scenarios.find(s=>s.id==='native-dafny-output-configuration')?.observation;errors.push(...require('./dafny-output.cjs').errors(o,config.runId));
  }else if(config.suite==='compiler-output'){const o=result.scenarios.find(s=>s.id==='native-compiler-output-configuration')?.observation;errors.push(...require('./compiler-output.cjs').errors(o,config.runId));
  }else if(config.suite==='output-lifecycle'){
    const observation=result.scenarios.find(s=>s.id==='native-output-restart')?.observation;errors.push(...outputLifecycleErrors(observation,config.target));
    const outputEvents=Array.isArray(observation?.events)?observation.events:[],panel=observation?.panel,readinessPrefix=config.target==='local'?'Solidity Lean is ready again':'Dafny is ready again.',metadata={uri:observation?.uri,version:observation?.version,sourceHash:observation?.sourceHash,sourceSession:outputEvents.find(e=>e.kind==='command.end'&&e.data?.id===(config.target==='local'?'solidityLean.restartServer':'dafny.restartServer'))?.data?.source?.session,channelId:observation?.channel?.data?.channelId,channel:config.target==='local'?'Solidity Lean':'Dafny VSCode',readinessPrefix,readinessLine:outputEvents.find(e=>e?.kind==='output'&&e.data?.channelId===observation?.channel?.data?.channelId&&e.data?.text?.startsWith(config.target==='local'?`Solidity Lean is ready again for ${observation.uri} (`:'Dafny is ready again.'))?.data.text.split('\n')[0]};
    if(panel?.runId!==config.runId||panel?.phase!=='output-channel'||panel?.status!=='captured'||panel?.metadataHash!==require('node:crypto').createHash('sha256').update(JSON.stringify(metadata)).digest('hex')||!panel?.capture?.captured||!panel?.capture?.screenshot||!panel?.capture?.output?.panelVisible||panel?.capture?.output?.selectedChannel!==metadata.channel||!metadata.readinessLine||!panel?.capture?.output?.text?.includes(metadata.readinessLine)||panel?.capture?.output?.readinessVisibility!=='not-certified'||!['before','after'].every(stage=>panel?.capture?.output?.[stage]?.visible&&panel.capture.output[stage].selectedChannel===metadata.channel&&panel.capture.output[stage].continuousText===panel.capture.output.text))errors.push('missing output panel/source DOM evidence');
    if(require('./output-visibility.cjs').errors(panel?.capture?.output?.glyphGeometry?.before,panel?.capture?.output?.glyphGeometry?.after,metadata.readinessLine||'',metadata.channel).length)errors.push('missing output character geometry/interval evidence');
    if(config.target==='local'){
      const feedback=observation?.feedback,expected=require('../src/status-summary.cjs').issueURL(feedback?.identity);
      if(!expected||feedback?.url!==expected||!outputEvents.some(event=>event?.kind==='output'&&event.data?.channelId===observation?.channel?.data?.channelId&&event.data?.text?.startsWith(`Solidity Lean is ready again for ${observation?.uri} (`)&&event.data.text.endsWith('\n'+expected)))errors.push('missing current restart issue draft');
      const lifecycle=observation?.resourceLifecycle,owned=e=>e?.kind==='output'&&e.data?.channel==='Solidity Lean'&&e.data?.channelId===observation?.channel?.data?.channelId,failures=Array.isArray(lifecycle?.failureEvents)?lifecycle.failureEvents:[],recovery=Array.isArray(lifecycle?.recoveryEvents)?lifecycle.recoveryEvents:[],reopen=lifecycle?.reopen;
      if(!lifecycle?.runtimeBefore||lifecycle.runtimeBeforeReported?.configuredPath!==lifecycle.runtimeBefore||lifecycle.runtimeRecoveredReported?.configuredPath!==lifecycle.runtimeBefore||!lifecycle.runtimeBeforeReported?.version||lifecycle.runtimeRecoveredReported?.version!==lifecycle.runtimeBeforeReported.version||typeof lifecycle?.rejectedRuntime!=='string'||!lifecycle.rejectedRuntime||lifecycle.runtimeBefore!==lifecycle.runtimeRestored||lifecycle.runtimeBefore===lifecycle.rejectedRuntime||!failures.some(e=>owned(e)&&e.data?.text?.startsWith(`Language server startup failed for ${observation?.uri}:`)&&e.data.text.includes(lifecycle.rejectedRuntime))||failures.some(e=>owned(e)&&e.data?.text?.startsWith('Solidity Lean is ready'))||!recovery.some(e=>owned(e)&&e.data?.text?.startsWith(`Solidity Lean is ready again for ${observation?.uri} (`))||typeof reopen?.beforeSynchronizationId!=='string'||!reopen.beforeSynchronizationId||typeof reopen?.afterSynchronizationId!=='string'||!reopen.afterSynchronizationId||reopen.beforeSynchronizationId===reopen.afterSynchronizationId||reopen.beforeOpenRecord?.direction!=='client'||reopen.beforeOpenRecord?.message?.method!=='textDocument/didOpen'||reopen.beforeOpenRecord?.message?.params?.textDocument?.uri!==observation?.uri||reopen.beforeOpenRecord?.message?.params?.textDocument?.version!==observation?.version||require('node:crypto').createHash('sha256').update(reopen.beforeOpenRecord?.message?.params?.textDocument?.text||'').digest('hex')!==observation?.sourceHash||reopen.beforeOpenRecord?.message?.params?.textDocument?.synchronizationId!==reopen.beforeSynchronizationId||reopen.openRecord?.message?.params?.textDocument?.synchronizationId!==reopen.afterSynchronizationId||!reopen?.beforeSession||!reopen?.afterSession||reopen.beforeSession===reopen.afterSession||!Number.isSafeInteger(reopen.openIndex)||!Number.isSafeInteger(reopen.closeIndex)||!(reopen.openIndex>reopen.closeIndex)||reopen.closeRecord?.direction!=='client'||reopen.openRecord?.direction!=='client'||reopen.closeRecord?.message?.method!=='textDocument/didClose'||reopen.closeRecord?.message?.params?.textDocument?.uri!==observation?.uri||reopen.openRecord?.message?.method!=='textDocument/didOpen'||reopen.openRecord?.message?.params?.textDocument?.uri!==observation?.uri||reopen.openRecord?.message?.params?.textDocument?.version!==observation?.version||require('node:crypto').createHash('sha256').update(reopen.openRecord?.message?.params?.textDocument?.text||'').digest('hex')!==observation?.sourceHash)errors.push('missing native runtime recovery/reopen ownership');
      const shutdown=observation?.shutdown,events=Array.isArray(shutdown?.events)?shutdown.events:[],disposed=events.map((event,index)=>({event,index})).filter(({event})=>event?.kind==='output.dispose'&&event.data?.channelId===observation?.channel?.data?.channelId&&event.data?.channel==='Solidity Lean');
      if(!Number.isSafeInteger(shutdown?.ownerPid)||!Array.isArray(shutdown?.children)||!shutdown.children.length||disposed.length!==1||!shutdown.children.every(child=>child.confirmedClose===true&&/^[0-9]+$/.test(child.birth||'')&&child.before?.birth===child.birth&&child.before?.ppid===shutdown.ownerPid&&child.before?.group===child.pid&&child.before?.session===child.pid&&Array.isArray(child.afterGroup)&&!child.afterGroup.length&&Array.isArray(child.workers)&&child.workers.every(worker=>Array.isArray(worker.afterGroup)&&!worker.afterGroup.length)&&events.some((event,index)=>index<disposed[0].index&&event?.kind==='output.shutdown.close'&&event.data?.pid===child.pid&&event.data?.birth===child.birth)))errors.push('missing confirmed local output retirement');
    }
  }else if(['proof-help','proof-hover'].includes(config.suite)){
    if(config.target!=='local'||!ids.includes('native-certified-proof-help'))errors.push('missing native certified proof-help observation');
    if(config.suite==='proof-hover'){
      const observation=result.scenarios.find(s=>s.id==='native-certified-proof-help')?.observation?.observations,popup=observation?.hoverPopup?.capture?.hoverPopup;
      if(!popup?.shown||!popup?.shownAfterCapture||!popup?.hidden||observation?.hoverPopup?.status!=='captured'||!observation.hoverPopup.capture?.screenshot||!Number.isInteger(observation?.hoverDuringVerification?.wire?.popupRequestIndex))errors.push('missing actual popup, dismissal or second wire observation');
      if(!observation?.actions||observation.actions.length!==2||!['guide','index'].every(choice=>observation.actions.some(a=>a.choice===choice&&a.menu?.status==='captured'&&a.menu.capture?.screenshot&&a.document?.status==='captured'&&a.document.capture?.screenshot)))errors.push('missing both native documentation actions');
    }

  }else if(config.suite==='trace-light-show'){
    if(config.target!=='dafny'||!ids.includes('native-trace-light-show-hide'))errors.push('missing native light trace observation');
  }else if(config.suite==='trace-visibility'){
    if(config.target!=='dafny'||!ids.includes('native-trace-tab-visibility-theme'))errors.push('missing native trace visibility observation');
  }else if(config.suite==='custom-import-actions'){
    if(!ids.includes('command-custom-import-actions'))errors.push('missing native compiler-only custom-import scenario');
    const o=result.scenarios?.find(s=>s.id==='command-custom-import-actions')?.observation;
    if(o?.request?.runId!==result.runId||!o?.request?.observation?.contextMenu?.rendered?.screenshot||!o.request.observation.prompt?.rendered?.screenshot||typeof o.request.observation.prompt.before?.value!=='string'||!o.request.observation.prompt.before.value||o.request.observation.prompt.before?.value!==o.request.observation.prompt.submitted?.value)errors.push('missing actual custom import menu/default prompt');
    if(config.target==='local'){
      const hash=require('node:crypto').createHash('sha256').update(o?.source||'').digest('hex'),a=o?.commandOwnership?.started,b=o?.commandOwnership?.completed;
      if(o?.report?.operation!=='buildCustomArgs'||o.report.kind!=='compiler-ast'||o.report.verification!=='not-run'||o.report.sourceHash!==hash||!a||!b||a.phase!=='started'||b.phase!=='completed'||a.operation!=='buildCustomArgs'||a.sourceHash!==hash||a.version!==o.version||b.commandId!==a.commandId||b.sourceSession!==a.sourceSession||b.artifact!==o.report.artifact||typeof o.report.source!=='string'||a.uri!==require('node:url').pathToFileURL(o.report.source).href||b.uri!==a.uri||b.version!==a.version||b.sourceHash!==a.sourceHash)errors.push('missing exact custom Build artifact/session ownership');
      const expectedOptions={includePaths:['vendor with spaces'],remappings:['alias/=lib/']};
      if(JSON.stringify(o?.report?.compilerOptions)!==JSON.stringify(expectedOptions)||o?.request?.observation?.prompt?.before?.value!==JSON.stringify(expectedOptions))errors.push('missing actual resource import defaults');
      const cancel=result.observations?.customCancellation;
      if(cancel?.request?.runId!==result.runId||!cancel?.request?.observation?.prompt?.cancelled?.rendered?.screenshot||typeof cancel.source!=='string'||cancel.sourceHash!==require('node:crypto').createHash('sha256').update(cancel.source).digest('hex')||cancel.version>=o?.version||cancel.sourceHash===hash||cancel.trusted!==true)errors.push('missing real custom prompt cancellation');
      const refusals=result.observations?.customInputRefusals;if(!Array.isArray(refusals)||refusals.length!==2||refusals[0]?.case!=='syntax'||refusals[1]?.case!=='options'||refusals.some(r=>r.uri!==a?.uri||r.version>=a?.version||r.sourceHash===hash||r.outputDirectory!==o?.report?.outputDirectory||require('./custom-input.cjs').refusalErrors(r,result.runId).length))errors.push('missing exact native custom input refusal observations');
    }else if(o?.terminal?.exitCode!==0||!o?.request?.observation?.prompt?.submitted?.value?.startsWith('build ')||o.request.observation.prompt.submitted.value.includes('--no-verify'))errors.push('missing authentic upstream custom Build terminal exit/profile');
  }else if(config.suite==='custom-default-commands'){
    if(!ids.includes('command-custom-default-build-keybinding'))errors.push('missing native default custom command scenario');
    if(config.target==='dafny'){for(const id of ['native-trace-show-copy-hide','native-dafny-run-action','native-dafny-test-action','native-trace-lifecycle'])if(!ids.includes(id))errors.push('missing native observation '+id);}
  } else if(config.suite==='custom-commands'){
    if(!ids.includes('command-custom-build-keybinding'))errors.push('missing native custom command scenario');
  } else if(config.suite==='commands'){
    if(!ids.includes('command-build-keybinding'))errors.push('missing native command scenario');
  } else if(config.suite==='visual') {
    // Visual capture has its own five scenarios. Missing early phases remain
    // missing, never passed checks; the aggregate below must retain those gaps.
    for(const id of ['visual-open','visual-first-feedback','visual-verified','visual-proof-broken','visual-proof-fixed'])
      if(!ids.includes(id))errors.push('missing visual scenario '+id);
  } else {
    if(!result.scenarios.some(s=>s.id==='initial-verification'))errors.push('missing initial verification scenario');
    if(['passed','passed-with-gaps'].includes(result.status)&&!result.scenarios.some(s=>s.id==='initial-verification'&&s.status==='passed'))errors.push('initial verification did not pass');
  }
  const passed=result.scenarios.filter(s=>s.status==='passed').map(s=>s.id).sort();
  if(JSON.stringify([...result.checks].sort())!==JSON.stringify(passed))errors.push('checks do not match passed scenarios');
  if(result.scenarios.some(s=>!['passed','partial','missing','unexamined','broken','timeout'].includes(s.status)))errors.push('invalid scenario status');
  const status=result.scenarios.some(s=>s.status==='timeout')?'timeout':result.scenarios.some(s=>s.status==='broken')?'broken':
    result.scenarios.every(s=>s.status==='passed')?'passed':'passed-with-gaps';
  // A fatal error outside a scenario may make a report worse, never better.
  if(result.status!==status&&!(['broken','timeout'].includes(result.status)&&result.error))errors.push('aggregate status contradicts scenarios');
  return errors;
}
module.exports = {scenarioFailure,validateHostResult,LspFrames, statistics, normalize, differences, ProcessSampler, summarize,scaling,protocol,hostEvidenceErrors,terminalSdkIdentity,outputLifecycleErrors};
