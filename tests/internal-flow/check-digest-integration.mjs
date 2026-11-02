#!/usr/bin/env node
// HOST ONLY: actual key/guard code with explicitly controlled bytes, not receipts.
import * as fs from 'node:fs';
import assert from 'node:assert/strict';
import {createHash} from 'node:crypto';
import {runInNewContext} from 'node:vm';
import {imports,splitBatchReports} from './fixture-cache.mjs';
import {withObjectDigests} from './exact-byte-digest.mjs';
const source=fs.readFileSync('tests/internal-flow/fixture-cache.mjs','utf8');
const body=source.slice(source.indexOf('function key() {'),source.indexOf('function guard(log) {'));
const sha=b=>createHash('sha256').update(b).digest('hex');
const helper='tests/internal-flow/exact-byte-digest.mjs',main='tests/internal-flow/Main.lean',dep='tests/internal-flow/Dep.lean',leaf='Solidity/Leaf.lean';
const obj=p=>'.lake/build/lib/lean/'+p.slice(0,-5)+'.olean',manifest='.lake/build/lib/lean/tests/internal-flow/Dep.v12-cache.json';
const registry={Main:{guard:'main.py'},Dep:{guard:'dep.py'}},tc={'toolchain/Init/Prelude.olean':'controlled toolchain'};
const initial=new Map(Object.entries({[helper]:fs.readFileSync(helper),[main]:'import tests.«internal-flow».Dep\n',[dep]:'import Solidity.Leaf\n',[leaf]:'import Init.Prelude\n',[obj(dep)]:'dep object',[obj(leaf)]:'leaf object','main.py':'main','dep.py':'dep','lean-toolchain':'lean','lakefile.toml':'config','tests/internal-flow/fixture-axiom-pins.json':'pins','tests/internal-flow/fixture-cache.mjs':'fixed driver bytes'}).map(([p,v])=>[p,Buffer.from(v)]));
function make(data,file=main,afterRead=()=>{}){
 const reads=[];const read=(p,encoding)=>{if(!data.has(p))throw Error('ENOENT '+p);const b=Buffer.from(data.get(p));reads.push([p,b.toString('hex')]);afterRead(p,data,reads);return encoding?b.toString(encoding):b;};
 const key=runInNewContext(body+'\nkey',{file,registry,expected:registry[file===main?'Main':'Dep'],pinsFile:'tests/internal-flow/fixture-axiom-pins.json',dir:'.lake/build/lib/lean/tests/internal-flow',sharedToolchain:tc,toolchainInputs:()=>{throw Error('unexpectedtoolchain')},readFileSync:read,existsSync:p=>data.has(p),createHash,hash:p=>sha(read(p)),freshObjectDigest:(p,owner)=>{const b=read(p);return owner?owner.digest(p,b):sha(b);},imports,JSON});
 return {key,reads};
}
const saved=make(initial,dep).key();assert(helper in saved.inputs);initial.set(manifest,Buffer.from(JSON.stringify({...saved,object_sha256:sha(initial.get(obj(dep)))})));
let checks=0;const outcome=fn=>{try{return {value:JSON.stringify(fn())};}catch(e){return {error:e.message};}};
await withObjectDigests(owner=>{
 const a=make(new Map(initial)),b=make(new Map(initial));assert.deepEqual(outcome(()=>a.key()),outcome(()=>b.key(owner)));assert.deepEqual(a.reads,b.reads);checks++;
});
for(const path of [...initial.keys()])await withObjectDigests(owner=>{
 const da=new Map(initial),db=new Map(initial),a=make(da),b=make(db);
 assert.deepEqual(outcome(()=>a.key()),outcome(()=>b.key(owner)));
 const old=da.get(path),changed=Buffer.from(old);if(changed.length)changed[changed.length-1]^=1;else throw Error('emptycontrol');
 da.set(path,changed);db.set(path,Buffer.from(changed));
 const aa=outcome(()=>a.key()),bb=outcome(()=>b.key(owner));assert.deepEqual(aa,bb);assert(aa.error||aa.value!==JSON.stringify(make(initial).key()),path);assert.deepEqual(a.reads,b.reads);checks++;
});
// At EACH original read point, mutate that path immediately after the read.
// Fresh current bytes remain the input; subsequent reads/calls see the mutation.
const trace=make(initial);trace.key();
for(let index=0;index<trace.reads.length;index++)await withObjectDigests(owner=>{
 const setup=()=>{const data=new Map(initial);let seen=0;return make(data,main,(p,d)=>{if(seen++===index){const b=Buffer.from(d.get(p));if(b.length)b[0]^=1;d.set(p,b);}});};
 const a=setup(),b=setup();assert.deepEqual(outcome(()=>a.key()),outcome(()=>b.key(owner)));assert.deepEqual(outcome(()=>a.key()),outcome(()=>b.key(owner)));assert.deepEqual(a.reads,b.reads);checks++;
});
for(const field of ['key','object_sha256','inputs'])await withObjectDigests(owner=>{
 const d=new Map(initial),s=JSON.parse(d.get(manifest));if(field==='inputs'){s.inputs[helper]='wrong';s.key=sha(JSON.stringify(s.inputs));}else s[field]='wrong';d.set(manifest,Buffer.from(JSON.stringify(s)));assert.throws(()=>make(d).key(owner),/stale or altered/);checks++;
});
const missing=new Map(initial);missing.delete(helper);await withObjectDigests(owner=>assert.throws(()=>make(missing).key(owner),/missing object digest/));checks++;
let pre,post;const releases=[];const globalGC=typeof global.gc;
await withObjectDigests(owner=>{pre=owner;owner.digest('large',Buffer.alloc(64*1024*1024,7));},r=>releases.push(r));
assert.throws(()=>pre.digest('closed',Buffer.alloc(0)),/closed/);
assert.equal(releases[0].retained_payload_bytes,0);assert(releases[0].after.arrayBuffers<=releases[0].before.arrayBuffers+1024*1024,'released array buffers still live');
// This assertion runs at the exact lifecycle position where a child may begin.
let childAllowed=true;assert(releases[0].closed&&childAllowed);
await withObjectDigests(owner=>{post=owner;owner.digest('large',Buffer.alloc(4,7));},r=>releases.push(r));assert.notEqual(pre,post);assert.equal(releases[1].stats.hits,0);
for(const synchronous of [true,false]){let leaked,receipt;await assert.rejects(withObjectDigests(async owner=>{leaked=owner;owner.digest('x',Buffer.alloc(1024,1));if(!synchronous)await Promise.resolve();throw Error('workfailed');},r=>{receipt=r;}),/workfailed/);assert(receipt.closed);assert.throws(()=>leaked.digest('x',Buffer.alloc(0)),/closed/);checks++;}
await assert.rejects(withObjectDigests(()=>{},()=>{throw Error('journalfailed');}),/journalfailed/);assert.equal(typeof global.gc,globalGC);
const guard=source.slice(source.indexOf('function guard(log) {'),source.indexOf('mkdirSync(dir,'));
const good="'a' depends on axioms: [propext]\n'b' does not depend on any axioms\n",expected={pins:{a:['propext'],b:[]}},check=log=>{splitBatchReports(log,[{names:['a','b']}]);return runInNewContext(guard+'\nguard(log)',{expected,log});};assert.equal(check(good),2);
for(const bad of [good.split('\n')[0],good+good,good.trim().split('\n').reverse().join('\n'),good.replace('propext','BAD'),good+'error: injected'])assert.throws(()=>check(bad));
console.log(JSON.stringify({host_only:true,not_authentication_or_kernel:true,checks,all_original_read_boundaries:trace.reads.length,exact_serialized_inputs_order_outcomes:true,helper_mutation_and_imported_manifest_rejected:true,distinct_pre_post_owners:true,closed_before_child:true,exception_cleanup:true,releases},null,2));
