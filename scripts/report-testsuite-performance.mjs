#!/usr/bin/env node
// Summarize completed, source-matched measurements; never substitute estimates.
import fs from 'node:fs';
import path from 'node:path';
import assert from 'node:assert/strict';
import {createHash} from 'node:crypto';
import os from 'node:os';
import {validateInputs} from './testsuite-performance.mjs';
const root=path.resolve('.'),input=path.join(root,'.lake/testsuite-performance');
const output=path.join(root,'docs/benchmarks/testsuite-2026-11-03');
const read=name=>JSON.parse(fs.readFileSync(path.join(input,name+'.json'),'utf8'));
const inputs=read('inputs');validateInputs(inputs);
const reports=Object.fromEntries(['native','extension','extension-wasm','browser','solkey'].map(k=>[k,read(k)]));
const median=values=>{const xs=[...values].sort((a,b)=>a-b);assert.ok(xs.length);return xs.length%2?xs[(xs.length-1)/2]:(xs[xs.length/2-1]+xs[xs.length/2])/2;};
const digest=file=>createHash('sha256').update(fs.readFileSync(file)).digest('hex');
for(const [kind,report] of Object.entries(reports)){
 assert.equal(report.passed,true,kind+' did not finish');
 const rows=report.trials.filter(t=>kind!=='solkey'||t.mode==='server');
 assert.equal(rows.length,inputs.count*(kind==='extension-wasm'?1:3));
 for(const row of rows){
  assert.equal(row.sourceHash,inputs.trials.find(t=>t.name===row.name)?.sourceHash,kind+': source mismatch');
  if(kind!=='solkey')assert.equal((kind==='native'?row.result.results:row.results)[0].status,'proved',kind+': '+row.name);
 }
}
assert.equal(reports.browser.assetBuild,JSON.parse(fs.readFileSync('web/single-file/build.json')).build);
const rows=inputs.trials.map(t=>{
 const matching=kind=>reports[kind].trials.filter(r=>r.name===t.name&&(kind!=='solkey'||r.mode==='server'));
 const key=matching('solkey');
 return {name:t.name,sourceHash:t.sourceHash,nativeMs:median(matching('native').map(r=>r.wallMs)),
  extensionMs:median(matching('extension').map(r=>r.wallMs)),extensionWasmMs:median(matching('extension-wasm').map(r=>r.wallMs)),
  browserMs:median(matching('browser').map(r=>r.wallMs)),solkeyMs:median(key.map(r=>r.wallMs)),
  solkeyProofMs:median(key.map(r=>r.results[0].millis)),solkeyStatuses:[...new Set(key.map(r=>r.results[0].status))]};
});
const summary={date:'2026-11-03',count:inputs.count,inventory:inputs.inventory,inventorySha256:inputs.inventorySha256,
 environment:{cpu:os.cpus()[0].model,cpuQuota:fs.readFileSync('/sys/fs/cgroup/cpu.max','utf8').trim(),node:process.version,platform:process.platform,arch:process.arch},
 startup:{nativeReadyMs:reports.native.startupMs,extensionInitializedMs:reports.extension.initializationMs,
  extensionFirstResultMs:reports.extension.initializationMs+reports.extension.trials[0].wallMs,
  browserReadyMs:reports.browser.startupMs,browserFirstResultMs:reports.browser.startupMs+reports.browser.trials[0].wallMs,
  solkeyColdResultMs:reports.solkey.trials.find(t=>t.mode==='cold').wallMs,solkeyServerMarkerMs:reports.solkey.serverStartupMs},
 medians:Object.fromEntries(['nativeMs','extensionMs','extensionWasmMs','browserMs','solkeyMs','solkeyProofMs'].map(k=>[k,median(rows.map(r=>r[k]))])),
 artifacts:Object.fromEntries(['web/single-file/index.html','.lake/artifacts/solidity-lean-0.5.5.vsix'].map(file=>[file,{bytes:fs.statSync(file).size,sha256:digest(file)}])),rows};
fs.mkdirSync(output,{recursive:true});
for(const [name,report] of Object.entries(reports))fs.writeFileSync(path.join(output,name+'.json'),JSON.stringify(report,null,2)+'\n');
fs.copyFileSync(path.join(input,'controls/results.json'),path.join(output,'controls.json'));
fs.copyFileSync('.lake/direct-native/build.json',path.join(output,'native-build.json'));
fs.copyFileSync('web/.lean-browser-build/direct/build.json',path.join(output,'wasm-build.json'));
fs.copyFileSync('web/single-file/build.json',path.join(output,'html-build.json'));
fs.writeFileSync(path.join(output,'workloads.json'),JSON.stringify({inventory:inputs.inventory,inventorySha256:inputs.inventorySha256,
 reading:inputs.reading,trials:inputs.trials.map(t=>({name:t.name,sourceHash:t.sourceHash,fixtureSha256:t.fixtureSha256,source:fs.readFileSync(t.source,'utf8')}))},null,2)+'\n');
fs.writeFileSync(path.join(output,'summary.json'),JSON.stringify(summary,null,2)+'\n');
const columns=['name','nativeMs','extensionMs','extensionWasmMs','browserMs','solkeyMs','solkeyProofMs','solkeyStatuses','sourceHash'];
fs.writeFileSync(path.join(output,'per-function.csv'),columns.join(',')+'\n'+rows.map(r=>columns.map(k=>typeof r[k]==='number'?r[k].toFixed(3):String(r[k])).join(',')).join('\n')+'\n');
console.log(JSON.stringify({startup:summary.startup,medians:summary.medians,solkeyOpen:rows.filter(r=>r.solkeyStatuses.some(s=>s!=='PROVED')).map(r=>r.name)},null,2));
