import fs from 'node:fs';
import assert from 'node:assert/strict';
import {spawn} from 'node:child_process';
import {createInterface} from 'node:readline';
import {createHash} from 'node:crypto';
const output='docs/benchmarks/directruntime-2026-11-04/hardening/startup-investigation.json';assert.ok(!fs.existsSync(output));
const executables={before:'.lake/direct-native/direct-check',hardening:'.lake/native-browser-hardening/native/direct-check'};
const trials=[];
for(let round=0;round<20;round++)for(const name of round%2?['hardening','before']:['before','hardening']){
 const begin=performance.now(),child=spawn(executables[name],[],{stdio:['pipe','pipe','pipe']});
 const exited=new Promise((resolve,reject)=>{child.once('exit',resolve);child.once('error',reject);});
 let error='';child.stderr.on('data',d=>error+=d);
 const ready=await new Promise((resolve,reject)=>{createInterface({input:child.stdout}).once('line',line=>{try{resolve(JSON.parse(line));}catch(e){reject(e);}});child.once('error',reject);child.once('exit',()=>reject(new Error(error)));});
 const wallMs=performance.now()-begin;assert.equal(ready.ready,true);child.kill();await exited;trials.push({round,name,wallMs});
}
const q=(a,p)=>a[Math.ceil(p*a.length)-1],summary={};
for(const name of Object.keys(executables)){const a=trials.filter(t=>t.name===name).map(t=>t.wallMs).sort((a,b)=>a-b);summary[name]={medianMs:(a[9]+a[10])/2,p95Ms:q(a,.95),samples:a.length};}
const ratio=summary.hardening.medianMs/summary.before.medianMs;
const report={boundary:'Alternating fresh-process ready handshake; warm filesystem cache, not machine-cold startup. No requests or proof verdicts counted.',executables:Object.fromEntries(Object.entries(executables).map(([n,p])=>[n,{path:p,sha256:createHash('sha256').update(fs.readFileSync(p)).digest('hex')}])),trials,summary,medianRatio:ratio,p95Ratio:summary.hardening.p95Ms/summary.before.p95Ms};
fs.writeFileSync(output,JSON.stringify(report,null,2)+'\n');console.log(JSON.stringify(report));
