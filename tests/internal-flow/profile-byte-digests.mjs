#!/usr/bin/env node
// HOST ONLY: exact key body, actual read-only inputs, actual stale failures.
// No synthetic dependency bindings, no Lean, no authentication/gate certificate.
import * as fs from 'node:fs';
import {createHash} from 'node:crypto';
import {runInNewContext} from 'node:vm';
import {performance} from 'node:perf_hooks';
import assert from 'node:assert/strict';
import {exactByteDigests} from './exact-byte-digest.mjs';
import {imports} from './fixture-cache.mjs';
const [baselinePath,output,mode='baseline']=process.argv.slice(2);
assert(baselinePath&&output?.startsWith('/')&&['baseline','compare'].includes(mode));
const baseline=fs.readFileSync(baselinePath,'utf8');
const body=s=>s.slice(s.indexOf('function key() {'),s.indexOf('function guard(log) {'));
const oldBody=body(baseline);
const beforeText='    inputs[path]=hash(path);\n    dependencies.push([dependency,JSON.parse(readFileSync(path,"utf8"))]);';
const afterText='    const bytes=readFileSync(path);\n    inputs[path]=createHash("sha256").update(bytes).digest("hex");\n    dependencies.push([dependency,JSON.parse(bytes.toString("utf8"))]);';
assert(oldBody.includes(beforeText));
const variants={before:oldBody,after:oldBody};
const registry=JSON.parse(fs.readFileSync('tests/internal-flow/fixture-axiom-pins.json','utf8'));
const files=Object.keys(registry).sort();assert.equal(files.length,27);assert.equal(Object.values(registry).reduce((n,e)=>n+Object.keys(e.pins).length,0),739);
const digest=b=>createHash('sha256').update(b).digest('hex');
const toolText=baseline.slice(baseline.indexOf('function toolchainInputs() {'),baseline.indexOf('// Production traversal'));
const tool=runInNewContext(toolText+'\ntoolchainInputs',{...fs,process,hash:p=>digest(fs.readFileSync(p))});
const ts=performance.now(),toolchain=tool(),toolchainBeforeMs=performance.now()-ts;
const classify=p=>p.endsWith('.v12-cache.json')?'manifest':p.endsWith('.olean')?'object':p.endsWith('.lean')&&!p.endsWith('lakefile.lean')?'source':p.endsWith('.py')?'guard':'config';
let invocation; let memo; let candidate=false;
function sample(bucket,kind,ms,bytes=0){const key=bucket+':'+kind;const row=invocation.phases[key]??={calls:0,ms:0,bytes:0};row.calls++;row.ms+=ms;row.bytes+=bytes;}
function read(path,encoding){const t=performance.now(),value=fs.readFileSync(path,encoding),elapsed=performance.now()-t;const n=Buffer.isBuffer(value)?value.length:Buffer.byteLength(value,encoding);sample('read',classify(path),elapsed,n);if(Buffer.isBuffer(value))invocation.origins.set(value,{kind:classify(path),path});if(classify(path)==='object'){const r=invocation.objects[path]??={reads:0,bytes:0,read_ms:0,hash_ms:0};r.reads++;r.bytes+=n;r.read_ms+=elapsed;}return value;}
function trackedHash(algorithm){const h=createHash(algorithm);let kind='other',origin,reused;
 return {update(value){origin=Buffer.isBuffer(value)?invocation.origins.get(value):null;kind=origin?.kind??(Buffer.isBuffer(value)?'other':'serialized-input');const t=performance.now();
 if(candidate&&kind==='object')reused=memo.digest(origin.path,value);else h.update(value);
 const dt=performance.now()-t;sample('hash-or-compare.update',kind,dt,Buffer.byteLength(value));if(kind==='object')invocation.objects[origin.path].hash_ms+=dt;return this;},
 digest(format){assert.equal(format,'hex');const t=performance.now(),value=reused??h.digest(format);sample('hash.digest',kind,performance.now()-t);return value;}};}
const json={parse(value){const t=performance.now(),result=JSON.parse(value);sample('json.parse','manifest',performance.now()-t,Buffer.byteLength(value));return result;},stringify(value){const t=performance.now(),result=JSON.stringify(value);sample('json.stringify','binding',performance.now()-t,Buffer.byteLength(result));return result;}};
const functions={};
for(const name of files)for(const variant of mode==='compare'?['before','after']:['before']){
 const observer='  __observeInputs(inputs);\n  for(const [dependency,saved] of dependencies) {';
 const code=variants[variant].replace('  for(const [dependency,saved] of dependencies) {',observer);assert(code.includes(observer));
 functions[name+variant]=runInNewContext(code+'\nkey',{file:`tests/internal-flow/${name}.lean`,pinsFile:'tests/internal-flow/fixture-axiom-pins.json',expected:registry[name],registry,dir:'.lake/build/lib/lean/tests/internal-flow',sharedToolchain:toolchain,
  toolchainInputs:()=>{throw Error('unexpected unshared snapshot')},readFileSync:read,existsSync:fs.existsSync,
  createHash:trackedHash,hash:p=>trackedHash('sha256').update(read(p)).digest('hex'),JSON:json,
  imports:text=>{const t=performance.now(),result=imports(text);sample('imports','pure-existing-parser',performance.now()-t,Buffer.byteLength(text));return result;},
  __observeInputs:inputs=>{invocation.inputs=inputs;},run:()=>{throw Error('FORBIDDEN_CHILD')},spawn:()=>{throw Error('FORBIDDEN_CHILD')}});
}
const rows=[],references=new Map();
for(let round=0;round<1;round++)for(const variant of mode==='compare'?(round%2?['after','before']:['before','after']):['before'])for(const name of files){
 if(name===files[0]){memo=exactByteDigests(512*1024*1024);candidate=variant==='after';}
 invocation={name,variant,round,phases:{},objects:{},origins:new WeakMap()};const t=performance.now();let returned,error;
 try{returned=functions[name+variant]();}catch(e){error={name:e.name,message:e.message};assert.match(e.message,/stale or altered checked fixture dependency/);}
 const elapsed=performance.now()-t;assert(invocation.inputs);
 // Snapshot/compare outside measured execution. The observer only retains the
 // actual complete inputs reference before validation, never mutates it.
 const serialized=JSON.stringify(invocation.inputs),outcome=JSON.stringify({returned:returned?.key,error});
 const comparable=serialized+'\n'+outcome;
 if(!references.has(name))references.set(name,comparable);else assert.equal(comparable,references.get(name),'key/input/order/failure mismatch '+name);
 const phases=invocation.phases,attributed=Object.values(phases).reduce((n,x)=>n+x.ms,0);
 rows.push({name,variant,round,elapsed_ms:elapsed,phases,objects:invocation.objects,memo:{...memo.stats},unattributed_ms:elapsed-attributed,input_entries:Object.keys(invocation.inputs).length,input_serialization_sha256:digest(serialized),actual_returned_key:returned?.key,error});
 invocation=null;
}
const ta=performance.now();assert.equal(JSON.stringify(tool()),JSON.stringify(toolchain));
const report={host_only:true,no_Lean:true,not_authentication_or_gate:true,mode,candidate_limit_bytes:512*1024*1024,candidate_scope:'one complete sweep, fresh read at every original point, private byte copies, exact Buffer.equals before digest reuse; no production change',fixture_count:27,registered_reports:739,fixtures:files,
 algorithm_source_sha256:digest(baseline),algorithm_scope:'Exact committed key body; only a nonmutating observer before binding validation and dependency wrappers for telemetry. Existing full shared toolchain snapshot is preserved, not a new optimization.',
 inputs_scope:'All actual source/object/guard/config/dependency-manifest bytes, no synthetic bindings or substituted oleans. Stale driver binding rejections are real; partial validation paths are NOT successful keys/authentication.',
 toolchain_entries:Object.keys(toolchain).length,toolchain_before_ms:toolchainBeforeMs,toolchain_after_ms:performance.now()-ta,complete_actual_toolchain_before_after_equal:true,
 byte_time_scope:'Fresh reads/crypto/imports/JSON are measured exclusively per invocation. Buffer-origin telemetry resets each call. Key residual includes decoding, validation/Object.entries, VM/wrapper/GC overhead; do not call it pure production/kernel time.',
 preserved_serialized_inputs_and_actual_result_or_failure:mode==='compare',rows};
fs.writeFileSync(output,JSON.stringify(report,null,2)+'\n');console.log(JSON.stringify({host_only:true,mode,rows:rows.length,output}));
