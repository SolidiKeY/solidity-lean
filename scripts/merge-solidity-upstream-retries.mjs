#!/usr/bin/env node
/** Merge isolated retries without losing either mode or its run provenance. */
import {readFileSync,writeFileSync,mkdirSync} from 'node:fs';
import {resolve,join,dirname} from 'node:path';
import {fileURLToPath} from 'node:url';
import {createHash} from 'node:crypto';
import {combineVariants,partition} from './solidity-upstream.mjs';

const read=path=>JSON.parse(readFileSync(path,'utf8'));
const save=(path,value)=>writeFileSync(path,JSON.stringify(value,null,2)+'\n');
const sha=bytes=>createHash('sha256').update(bytes).digest('hex');
const identity=['version','commit','compiler','compilerSha256','archiveSha256','runnerSha256',
  'modelSha256','evmVersion','loopFuel','scope','snapshotFiles'];

export function mergeRetry(original,retry) {
  if (original.path!==retry.path || original.stage!=='lean-runtime' || retry.stage!=='lean-runtime' ||
      JSON.stringify(original.requiredPipelines)!==JSON.stringify(retry.requiredPipelines))
    throw new Error('retry changes fixture identity or required source modes');
  if (!original.variants || !retry.variants) throw new Error('retry lacks mode observations');
  const variants=new Map(original.variants.map(row=>[row.pipeline,row]));
  for (const row of retry.variants) {
    if (!original.requiredPipelines.includes(row.pipeline)) throw new Error('unexpected retry mode');
    const before=variants.get(row.pipeline);
    if (before && before.status!=='blocked' && row.status!=='blocked' && before.status!==row.status)
      throw new Error('retry contradicts an already conclusive verdict');
    if (!before || before.status==='blocked') variants.set(row.pipeline,row);
  }
  return combineVariants(original.path,original.requiredPipelines,[...variants.values()]);
}

export function compatible(base,retry) {
  for (const key of identity) if (JSON.stringify(base[key])!==JSON.stringify(retry[key]))
    throw new Error('retry provenance differs: '+key);
}

export function mergeDirectories(args) {
  if (args.length<2) throw new Error('usage: merge-solidity-upstream-retries.mjs RESULTS_DIR RETRY_RESULTS_DIR ...');
  const [output,...directories]=args.map(path=>resolve(path));
  const report=read(join(output,'results.json'));
  const summary=read(join(output,'summary.json'));
  if (!summary.complete) throw new Error('finish the original run before merging retries');
  const rows=new Map(report.results.map(row=>[row.path,row]));
  const references=new Map((report.retryReports ?? []).map(ref=>[ref.path,ref]));
  mkdirSync(join(output,'retries'),{recursive:true});
  for (const directory of directories) {
    const bytes=readFileSync(join(directory,'results.json'));
    const retry=JSON.parse(bytes);
    const retrySummary=read(join(directory,'summary.json'));
    compatible(report.metadata,retry.metadata);
    if (!retrySummary.complete || retry.results.length!==1 || retry.metadata.filter!==retry.results[0].path)
      throw new Error('expected one complete isolated fixture retry');
    const row=retry.results[0], before=rows.get(row.path);
    if (!before) throw new Error('retry is outside the original selection');
    rows.set(row.path,mergeRetry(before,row));
    const path='retries/'+sha(bytes)+'.json';
    writeFileSync(join(output,path),bytes);
    references.set(path,{path,sha256:sha(bytes),fixture:row.path,
      timeoutMs:retry.metadata.timeoutMs,batchSize:retry.metadata.batchSize});
  }
  const results=[...rows.values()].sort((a,b)=>a.path.localeCompare(b.path));
  const groups=partition(results),stages={};
  for (const row of results) {stages[row.stage]??={working:0,broken:0,blocked:0};stages[row.stage][row.status]++;}
  const retryReports=[...references.values()].sort((a,b)=>a.path.localeCompare(b.path));
  const retryMergeSha256=sha(readFileSync(fileURLToPath(import.meta.url)));
  save(join(output,'results.json'),{metadata:report.metadata,results,retryReports,retryMergeSha256});
  save(join(output,'summary.json'),{...summary,stages,
    counts:Object.fromEntries(Object.entries(groups).map(([key,values])=>[key,values.length])),retryReports,retryMergeSha256});
  for (const [name,values] of Object.entries(groups)) {
    save(join(output,name+'.json'),values);
    writeFileSync(join(output,name+'.txt'),values.map(row=>`${row.path}\t${row.stage}\t${row.reason}`).join('\n')+'\n');
  }
  const coverage=read(join(output,'file-coverage.json')).map(file=>{
    const row=rows.get(file.path);
    return row ? {...file,status:row.status,reason:row.reason} : file;
  });
  save(join(output,'file-coverage.json'),coverage);
  return Object.fromEntries(Object.entries(groups).map(([key,values])=>[key,values.length]));
}

if (process.argv[1] && resolve(process.argv[1])===fileURLToPath(import.meta.url)) {
  try {console.log(JSON.stringify(mergeDirectories(process.argv.slice(2))));}
  catch(error) {console.error(error.stack);process.exitCode=2;}
}
