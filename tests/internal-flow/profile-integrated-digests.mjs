#!/usr/bin/env node
// HOST ONLY: exact FINAL key algorithm/real inputs, no manifest rebinding/Lean.
import * as fs from 'node:fs';
import {createHash} from 'node:crypto';
import {runInNewContext} from 'node:vm';
import {performance} from 'node:perf_hooks';
import assert from 'node:assert/strict';
import {imports} from './fixture-cache.mjs';
import {withObjectDigests} from './exact-byte-digest.mjs';
const output=process.argv[2];assert(output?.startsWith('/'));
const source=fs.readFileSync('tests/internal-flow/fixture-cache.mjs','utf8');
const helper=fs.readFileSync('tests/internal-flow/exact-byte-digest.mjs');
const digest=b=>createHash('sha256').update(b).digest('hex');
const hash=p=>digest(fs.readFileSync(p));
const registry=JSON.parse(fs.readFileSync('tests/internal-flow/fixture-axiom-pins.json','utf8'));
const files=Object.keys(registry).sort();assert.equal(files.length,27);assert.equal(Object.values(registry).reduce((n,x)=>n+Object.keys(x.pins).length,0),739);
const toolText=source.slice(source.indexOf('function toolchainInputs() {'),source.indexOf('// Production traversal'));
const tool=runInNewContext(toolText+'\ntoolchainInputs',{...fs,process,hash});
const t0=performance.now(),toolchain=tool(),beforeMs=performance.now()-t0;
const body=source.slice(source.indexOf('function key() {'),source.indexOf('function guard(log) {'));
const marker='  for(const [dependency,saved] of dependencies) {';assert(body.includes(marker));
let current;const functions={};
for(const name of files)functions[name]=runInNewContext(body.replace(marker,'  observeInputs(inputs);\n'+marker)+'\nkey',{
 file:`tests/internal-flow/${name}.lean`,pinsFile:'tests/internal-flow/fixture-axiom-pins.json',expected:registry[name],registry,dir:'.lake/build/lib/lean/tests/internal-flow',sharedToolchain:toolchain,toolchainInputs:()=>{throw Error('unshared toolchain')},
 readFileSync:fs.readFileSync,existsSync:fs.existsSync,createHash,hash,JSON,imports,
 freshObjectDigest:(path,owner)=>{const t=performance.now(),bytes=fs.readFileSync(path);current.read_ms+=performance.now()-t;current.reads++;current.bytes+=bytes.length;const h=performance.now();const value=owner?owner.digest(path,bytes):digest(bytes);current.digest_ms+=performance.now()-h;return value;},observeInputs:x=>{current.inputs=x;},run:()=>{throw Error('FORBIDDEN_CHILD')}});
const references=new Map(),sweeps=[];
for(let round=0;round<2;round++)for(const variant of round?['candidate','ordinary']:['ordinary','candidate']){
 const rows=[];let release;const start=performance.now();
 const work=owner=>{for(const name of files){current={name,read_ms:0,digest_ms:0,reads:0,bytes:0};const t=performance.now();let returned,error;try{returned=functions[name](owner);}catch(e){error={name:e.name,message:e.message};assert.match(e.message,/stale or altered checked fixture dependency/);}
 const elapsed=performance.now()-t;assert(current.inputs);const serialized=JSON.stringify(current.inputs),outcome=JSON.stringify({returned:returned?.key,error});const comparable=serialized+'\n'+outcome;if(references.has(name))assert.equal(comparable,references.get(name));else references.set(name,comparable);
 assert.equal(current.inputs['tests/internal-flow/exact-byte-digest.mjs'],digest(helper));
 rows.push({...current,inputs:undefined,elapsed_ms:elapsed,serialized_sha256:digest(serialized),returned_key:returned?.key,error});current=null;}};
 if(variant==='candidate')await withObjectDigests(work,r=>{release=r;});else work(null);
 sweeps.push({round,variant,elapsed_including_cleanup_ms:performance.now()-start,rows,release});
}
const t1=performance.now();assert.equal(JSON.stringify(tool()),JSON.stringify(toolchain));
fs.writeFileSync(output,JSON.stringify({host_only:true,no_Lean:true,not_authentication_or_gate:true,final_driver_sha256:digest(source),final_helper_sha256:digest(helper),toolchain_entries:Object.keys(toolchain).length,toolchain_before_ms:beforeMs,toolchain_after_ms:performance.now()-t1,full_toolchain_equal:true,all27_exact_ordered_inputs_and_outcomes_equal:true,scope:'Two paired sweeps with reverse order, final512MiB/4096entry helper, actual synchronous cleanup included. Equality wrappers/time/GC/warmorder remain measurement overhead; not combined Lean/report/postcheck headroom.',sweeps},null,2)+'\n');
console.log(JSON.stringify({host_only:true,output,sweeps:sweeps.map(s=>({variant:s.variant,round:s.round,ms:s.elapsed_including_cleanup_ms}))}));
