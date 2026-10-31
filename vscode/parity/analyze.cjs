#!/usr/bin/env node
'use strict';
const {readFileSync,writeFileSync,existsSync,mkdirSync}=require('node:fs');
const {resolve,join,relative,dirname,basename}=require('node:path');
const repo=resolve(__dirname,'../..');

/** Separate solver activity from frontend/server activity in the retained raw
 * samples. A living solver is not evidence that it consumed CPU. */
function activity(resources) {
  if(resources.platform!=='linux')return {status:'unexamined'};
  const old=new Map();let peakSolvers=0,activeSolvers=0,activeLean=0;
  for(const sample of resources.samples||[]) {
    let solvers=0,solverCpu=0,leanCpu=0;
    for(const process of sample.processes) {
      const previous=old.get(process.pid),active=previous!==undefined&&process.ticks>previous;
      if(/^z3(?:-|$)/.test(process.name)){solvers++;if(active)solverCpu++;}
      if(process.name==='lean'&&active)leanCpu++;
      old.set(process.pid,process.ticks);
    }
    peakSolvers=Math.max(peakSolvers,solvers);activeSolvers=Math.max(activeSolvers,solverCpu);activeLean=Math.max(activeLean,leanCpu);
  }
  return {status:'observed',peakLivingSolverProcesses:peakSolvers,maxCpuActiveSolverProcesses:activeSolvers,maxCpuActiveLeanProcesses:activeLean,
    scope:'Entire scenario suite. Distinct processes accrued ticks in the same sample interval; this does not prove simultaneous instructions or isolate the initial-verification phase.'};
}
function build(paths,invalidatedPaths=[]) {
  const datasets=paths.map(path=>{
    const report=JSON.parse(readFileSync(path,'utf8'));
    return {label:basename(dirname(resolve(path))),path:relative(repo,resolve(path)),status:report.status,started:report.started,finished:report.finished,options:report.options,
      environment:report.environment,summary:report.summary,parallelScaling:report.parallelScaling,
      runs:report.runs.map(run=>({target:run.target,suite:run.suite,workers:run.workers,cache:run.cache,trial:run.trial,warmup:run.warmup,status:run.status,
        leanNumThreads:JSON.parse(readFileSync(join(run.artifacts,'config.json'),'utf8')).runtimeEnvironment?.LEAN_NUM_THREADS??null,
        artifact:relative(repo,join(run.artifacts,'result.json')),metrics:run.result?.metrics||{},renderer:run.renderer,
        resources:run.resources,solverActivity:activity(JSON.parse(readFileSync(join(run.artifacts,'resources.json'),'utf8'))),protocol:run.protocol,
        scenarios:(run.result?.scenarios||[]).map(s=>({id:s.id,status:s.status,error:s.error?.split('\n')[0],scope:s.observation?.scope}))})),
      comparisons:report.comparisons.map(c=>({scenario:c.scenario,workers:c.workers,cache:c.cache,trial:c.trial,differenceCount:c.differences.length})),
      featureParity:report.featureParity.map(f=>({...f,evidence:f.evidence.map(e=>({...e,artifact:relative(repo,e.artifact)}))})),
      limitations:report.limitations};
  });
  const runs=datasets.flatMap(d=>d.runs),measured=runs.filter(r=>!r.warmup);
  const fullPath=paths.find((_,i)=>datasets[i].options.suite==='full');
  let diagnostics={},saveEditRace,uiDifference={},serverCapabilities={};
  if(fullPath){const report=JSON.parse(readFileSync(fullPath,'utf8'));for(const run of report.runs){
    const observation=run.result?.scenarios.find(s=>s.id==='failure-diagnostics')?.observation;
    if(observation)diagnostics[run.target]={severities:observation.diagnostics.map(d=>d.severity),outcomes:observation.outcomes};
    if(run.target==='local')saveEditRace=run.result?.scenarios.find(s=>s.id==='save-edit-race');
    uiDifference[run.target]={commands:run.result?.observations.commands||[],decorationTypeCount:run.result?.observations.decorations?.length,
      editorCount:run.renderer?.editorCount,accessibilityNodes:run.renderer?.accessibilityNodes,
      visibleStateArtifact:relative(repo,join(run.artifacts,'visible-state.json'))};
    serverCapabilities[run.target]=run.result?.observations.serverCapabilities||{status:'unexamined'};
  }}
  const sizes=[...new Set(datasets.map(d=>d.options.obligations))].join(', ');
  const latencyRatios=datasets.filter(d=>d.options.suite==='benchmark').flatMap(dataset=>dataset.summary.filter(r=>r.target==='dafny').flatMap(reference=>{
    const candidate=dataset.summary.find(r=>r.target==='local'&&r.workers===reference.workers&&r.cache===reference.cache);
    if(!candidate)return [];
    const ratio=key=>candidate?.metrics[key]?.median&&reference.metrics[key]?.median?candidate.metrics[key].median/reference.metrics[key].median:null;
    return [{dataset:dataset.label,workers:reference.workers,cache:reference.cache,initialLocalOverDafny:ratio('initialVerificationMs'),incrementalLocalOverDafny:ratio('incrementalVerificationMs'),
      scope:'End-to-end shared-fragment latency, including different frontend/persistence architectures. This is not a solver-speed ratio.'}];
  }));
  const invalidatedDatasets=invalidatedPaths.map(path=>{
    const report=JSON.parse(readFileSync(path,'utf8'));
    return {path:relative(repo,resolve(path)),status:report.status,reason:'Pre-fix editor IPC path exceeded the Unix socket-path limit. Excluded from performance estimates and rerun with short temporary editor state.',
      launches:report.runs.length,broken:report.runs.filter(r=>!['passed','passed-with-gaps'].includes(r.status)).length,
      runs:report.runs.map(r=>({target:r.target,trial:r.trial,status:r.status,error:r.error,log:relative(repo,join(r.artifacts,'editor.log'))}))};
  });
  return {schemaVersion:1,generated:new Date().toISOString(),fullParityEstablished:false,
    counts:{launches:runs.length,measuredTrials:measured.length,warmups:runs.length-measured.length,
      broken:runs.filter(r=>!['passed','passed-with-gaps'].includes(r.status)).length},
    datasets,invalidatedDatasets,latencyRatios,diagnosticDifference:diagnostics,saveEditRace,uiDifference,serverCapabilities,
    interpretation:[`The paired workloads use ${sizes} constant-return functions; the incremental case adds one function.`,
      'Fresh process/profile startup and live-server incremental verification are separate. OS caches were not flushed.',
      'The local LSP bounds concurrent files with 1–4 workers. Within-file proofs remain serial. Exact-snapshot cache hits and changed-buffer checks are separate; Dafny cache policies have no equivalent local selector.',
      'Solver overlap is derived from distinct process CPU deltas, not task counts or async calls. A native Lean LSP can include server and file-worker processes; CPU-active Lean processes are not a proof-worker count.',
      'Dafny owns a Boogie engine per project; Boogie 3.5.5 applies VcsCores using a per-engine semaphore. Requested workers are not a global server-wide solver cap.',
      'The editor cancellation metric measures acknowledgement; separate real LSP tests check worker termination. Complex proofs, renderer paint latency and single-declaration assertion-split scaling remain unexamined.',
      'Three measurement repetitions give descriptive medians and nearest-rank p95, not a stable tail-latency estimate.']};
}
function markdown(baseline,jsonName='baseline.json') {
  const lines=['# Measured editor baseline','',`Recorded ${baseline.generated}. Full parity is **not established**.`,
    '',`${baseline.counts.launches} isolated editor launches; ${baseline.counts.measuredTrials} measured trials; ${baseline.counts.warmups} warmups; ${baseline.counts.broken} broken launches.`,
    '', '| Dataset | Target | Workers requested | Cache requested | n | Initial median / p95 ms | Incremental median / p95 ms |',
    '|---|---|---:|---|---:|---:|---:|'];
  const format=metric=>metric?.median===null||metric?.median===undefined?'unmeasured':`${metric.median.toFixed(1)} / ${metric.p95.toFixed(1)}`;
  for(const dataset of baseline.datasets)for(const row of dataset.summary)lines.push(`| ${dataset.label} | ${row.target} | ${row.workers} | ${row.cache} | ${row.trials} | ${format(row.metrics.initialVerificationMs)} | ${format(row.metrics.incrementalVerificationMs)} |`);
  lines.push('', '| Dataset | Target | Workers | Exact-snapshot cache median / p95 ms | Two-file median / p95 ms |', '|---|---|---:|---:|---:|');
  for(const dataset of baseline.datasets)for(const row of dataset.summary)lines.push(`| ${dataset.label} | ${row.target} | ${row.workers} | ${format(row.metrics.warmVerificationMs)} | ${format(row.metrics.crossFileVerificationMs)} |`);
  lines.push('','| Dataset | Workers requested | Cache requested | Local / Dafny initial latency | Local / Dafny incremental latency |','|---|---:|---|---:|---:|',
    ...baseline.latencyRatios.map(r=>`| ${r.dataset} | ${r.workers} | ${r.cache} | ${r.initialLocalOverDafny?.toFixed(2)??'unmeasured'}× | ${r.incrementalLocalOverDafny?.toFixed(2)??'unmeasured'}× |`),
    '', 'Ratios include frontend and process architecture differences. They do not compare pure solver execution speed.');
  lines.push('','## Observed process overlap','', '| Target | Workers | Cache | Maximum CPU-active Z3 processes | Maximum CPU-active Lean processes |', '|---|---:|---|---:|---:|');
  const grouped=new Map();
  for(const run of baseline.datasets.flatMap(d=>d.runs).filter(r=>!r.warmup)){
    const key=JSON.stringify([run.target,run.workers,run.cache]);if(!grouped.has(key))grouped.set(key,[]);grouped.get(key).push(run);
  }
  for(const rows of grouped.values())lines.push(`| ${rows[0].target} | ${rows[0].workers} | ${rows[0].cache} | ${Math.max(...rows.map(r=>r.solverActivity.maxCpuActiveSolverProcesses??0))} | ${Math.max(...rows.map(r=>r.solverActivity.maxCpuActiveLeanProcesses??0))} |`);
  lines.push('','These counts cover the complete scenario suite, including concurrent files and cancellation. They show CPU activity within sampling intervals, not exact simultaneous instructions or isolated phase throughput.',
    '', '## Scope and interpretation','',...baseline.interpretation.map(s=>'- '+s),
    '', '## Artifacts','',...baseline.datasets.map(d=>`- ${d.path}: ${d.status}; source hashes, exact configuration and raw trial references are retained in the JSON baseline.`),
    ...baseline.invalidatedDatasets.map(d=>`- Invalidated ${d.path}: ${d.broken} failed starts across ${d.launches} attempts. ${d.reason}`),
    '', 'The [machine-readable baseline]('+jsonName+') retains individual timings, dispersion, timeout rates, resource activity, scenario classifications, protocol summaries and feature evidence. Raw traces and renderer artifacts are referenced under `.cache/editor-parity/`; rerun the [harness](../../docs/dafny-editor-parity.md) when those workspace artifacts are unavailable.','');
  return lines.join('\n');
}
function main(args=process.argv.slice(2)) {
  const outputIndex=args.indexOf('--output');
  if(outputIndex<0||!args[outputIndex+1])throw new Error('Use --output FILE.json REPORT.json [REPORT.json ...]');
  const output=resolve(args[outputIndex+1]);args.splice(outputIndex,2);
  const invalidated=[];
  while(args.includes('--invalidated')){const i=args.indexOf('--invalidated');if(!args[i+1])throw new Error('Missing invalidated report');invalidated.push(args[i+1]);args.splice(i,2);}
  if(!args.length||args.some(p=>!existsSync(p)))throw new Error('Missing input reports');
  const baseline=build(args,invalidated);mkdirSync(dirname(output),{recursive:true});
  writeFileSync(output,JSON.stringify(baseline,null,2)+'\n');writeFileSync(output.replace(/\.json$/,'.md'),markdown(baseline,basename(output)));
  process.stdout.write(output+'\n');
}
module.exports={activity,build,markdown};
if(require.main===module)try{main();}catch(error){process.stderr.write(error.stack+'\n');process.exitCode=1;}
