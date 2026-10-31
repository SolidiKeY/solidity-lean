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
    const table = procTable(), ids = new Set([this.root]);
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
      activeCpuProcesses,activeVerifierProcesses,processes:rows.map(({pid,ppid,name,ticks,rssBytes})=>({pid,ppid,name,ticks,rssBytes}))});
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
    const metrics = [...new Set(rows.flatMap(r=>Object.keys(r.result?.metrics || {})))];
    return {target:rows[0].target,workers:rows[0].workers,cache:rows[0].cache,suite:rows[0].suite,trials:rows.length,
      failures:rows.filter(r=>!['passed','passed-with-gaps'].includes(r.status)).length,
      capabilityGaps:rows.reduce((s,r)=>s+(r.result?.scenarios?.filter(t=>['missing','partial','unexamined'].includes(t.status)).length||0),0),
      timeoutRate:rows.filter(r=>r.status === 'timeout').length/rows.length,
      metrics:Object.fromEntries(metrics.map(key=>[key,statistics(rows.map(r=>r.result?.metrics[key]))])),
      peakRssBytes:statistics(rows.map(r=>r.resources?.peakRssBytes)),cpuTicks:statistics(rows.map(r=>r.resources?.cpuTicks)),
      cpuSeconds:statistics(rows.map(r=>r.resources?.cpuSeconds)),averageCpuCores:statistics(rows.map(r=>r.resources?.averageCpuCores)),
      activeVerifierProcesses:statistics(rows.map(r=>r.resources?.maxActiveVerifierProcesses))};
  });
}
function scaling(summary) {
  return summary.map(row=>{
    const baseline=summary.find(s=>s.target===row.target&&s.cache===row.cache&&s.suite===row.suite&&s.workers===1);
    const latency=row.metrics.initialVerificationMs?.median,base=baseline?.metrics.initialVerificationMs?.median;
    return {target:row.target,cache:row.cache,workers:row.workers,baselineWorkers:1,
      speedup:row.target==='dafny'&&base&&latency?base/latency:null,
      efficiency:row.target==='dafny'&&base&&latency?base/latency/row.workers:null,
      scope:row.target==='dafny'?'End-to-end within-file declaration workload; frontend serialization and startup are included.':'Worker setting unsupported; no scaling claim.'};
  });
}
function protocol(tracePath) {
  if(!tracePath)return {status:'unexamined',reason:'Tracing disabled'};
  let records;try{records=readFileSync(tracePath,'utf8').trim().split('\n').filter(Boolean).map(l=>JSON.parse(l));}
  catch(error){return {status:'unexamined',reason:error.message};}
  const methods={},errors=[],states=new Map(),queueMs=[],executionMs=[];
  for(const record of records) {
    if(record.error){errors.push(record.error);continue;}
    const message=record.message,method=message?.method;
    if(method)methods[record.direction+':'+method]=(methods[record.direction+':'+method]||0)+1;
    if(message?.error)errors.push(message.error);
    if(method==='dafny/textDocument/symbolStatus')for(const symbol of message.params.namedVerifiables) {
      const key=JSON.stringify([message.params.uri,message.params.version,symbol.nameRange]),previous=states.get(key)||{};
      if(symbol.status===1&&previous.queued===undefined)previous.queued=record.time;
      if(symbol.status===2&&previous.running===undefined){previous.running=record.time;if(previous.queued!==undefined)queueMs.push(record.time-previous.queued);}
      if(symbol.status>=4&&!previous.done){previous.done=true;if(previous.running!==undefined)executionMs.push(record.time-previous.running);}
      states.set(key,previous);
    }
  }
  return {status:'observed',methods,errors,queueMs:statistics(queueMs),symbolExecutionMs:statistics(executionMs),
    scope:'Native status notification intervals include transport and notification throttling; they do not isolate pure solver or VC time.'};
}
module.exports = {LspFrames, statistics, normalize, differences, ProcessSampler, summarize,scaling,protocol};
