#!/usr/bin/env node
// HOST ONLY experiment controls, never production receipts or Lean evidence.
import * as fs from 'node:fs';
import {createHash} from 'node:crypto';
import {runInNewContext} from 'node:vm';
import assert from 'node:assert/strict';
import {exactByteDigests} from './exact-byte-digest.mjs';
import {imports,splitBatchReports} from './fixture-cache.mjs';
const source=fs.readFileSync(process.argv[2],'utf8');
const body=source.slice(source.indexOf('function key() {'),source.indexOf('function guard(log) {'));
const old='    inputs[path]=hash(path);\n    dependencies.push([dependency,JSON.parse(readFileSync(path,"utf8"))]);';
const replacement='    const bytes=readFileSync(path);\n    inputs[path]=createHash("sha256").update(bytes).digest("hex");\n    dependencies.push([dependency,JSON.parse(bytes.toString("utf8"))]);';assert(body.includes(old));
const root='tests/internal-flow/Root.lean',dep='tests/internal-flow/Dep.lean',leaf='Solidity/Leaf.lean',manifest='.lake/build/lib/lean/tests/internal-flow/Dep.v12-cache.json';
const obj=p=>'.lake/build/lib/lean/'+p.slice(0,-5)+'.olean',digest=b=>createHash('sha256').update(b).digest('hex');
const registry={Root:{guard:'root.py'},Dep:{guard:'dep.py'}},tc={'toolchain/Init/Prelude.olean':'fixed test value'};
const files=new Map(Object.entries({[root]:'import tests.«internal-flow».Dep\n',[dep]:'import Solidity.Leaf\n',[leaf]:'import Init.Prelude\n',[obj(dep)]:'dep object',[obj(leaf)]:'leaf object','root.py':'guard','dep.py':'guard','tests/internal-flow/fixture-axiom-pins.json':'pins','tests/internal-flow/fixture-cache.mjs':'identical test bytes','lean-toolchain':'lean','lakefile.toml':'config'}).map(([p,b])=>[p,Buffer.from(b)]));
function make(code,data,file=root,afterRead=null){const reads=[];const memo=exactByteDigests(16);const read=(p,encoding)=>{assert(data.has(p),'missing '+p);const b=Buffer.from(data.get(p));reads.push(p);afterRead?.(p,data,reads);return encoding?b.toString(encoding):b;};return {reads,key:runInNewContext(code+'\nkey',{file,registry,expected:registry[file===root?'Root':'Dep'],pinsFile:'tests/internal-flow/fixture-axiom-pins.json',dir:'.lake/build/lib/lean/tests/internal-flow',sharedToolchain:tc,toolchainInputs:()=>{throw Error('test snapshot required')},imports,readFileSync:read,existsSync:p=>data.has(p),createHash,hash:p=>{const b=read(p);return code.endsWith('// exact digest candidate')&&p.endsWith('.olean')?memo.digest(p,b):digest(b);}})};}
const saved=make(body,files,dep).key();files.set(manifest,Buffer.from(JSON.stringify({...saved,object_sha256:digest(files.get(obj(dep)))})));
const candidate=body+'\n// exact digest candidate',before=make(body,new Map(files)),after=make(candidate,new Map(files));
assert.equal(JSON.stringify(before.key()),JSON.stringify(after.key()));assert.equal(before.reads.filter(p=>p===manifest).length,2);assert.equal(after.reads.filter(p=>p===manifest).length,2);
const rows=[];
for(const code of [body,candidate])for(const path of [root,dep,leaf,obj(dep),obj(leaf),'root.py','dep.py','lean-toolchain','tests/internal-flow/fixture-cache.mjs',manifest]){
 const data=new Map(files),h=make(code,data),a=h.key();data.set(path,Buffer.concat([data.get(path),Buffer.from('\nchanged')]));let rejected=false;try{rejected=h.key().key!==a.key}catch{rejected=true}assert(rejected,path);rows.push({variant:code===body?'committed':'candidate',mutation:path,rejected:true});
}
for(const code of [body,candidate])for(const field of ['key','object_sha256','inputs']){
 const data=new Map(files),bad=JSON.parse(data.get(manifest));
 if(field==='inputs'){bad.inputs['lean-toolchain']='wrong';bad.key=digest(JSON.stringify(bad.inputs));}else bad[field]='wrong';
 data.set(manifest,Buffer.from(JSON.stringify(bad)));assert.throws(()=>make(code,data).key(),/stale or altered/);
 rows.push({variant:code===body?'committed':'candidate',self_consistent_corruption:field,rejected:true});
}
// Preserve the ORIGINAL two-read manifest boundary exactly. Both variants
// see the changed second read and reject it; digest reuse applies only to objects.
for(const code of [body,candidate]){
 const data=new Map(files),oldBytes=data.get(manifest),bad=JSON.parse(oldBytes);bad.key='wrong';
 const h=make(code,data,root,(p,d,reads)=>{if(p===manifest&&reads.filter(x=>x===manifest).length===1)d.set(p,Buffer.from(JSON.stringify(bad)));});
 let failed=false;try{h.key()}catch{failed=true}assert.equal(failed,true);
 assert.throws(()=>h.key(),/stale or altered/);
 rows.push({variant:code===body?'committed':'candidate',original_two_read_manifest_boundary:true,first_call_rejected:failed,next_call_rejected:true});
}
const guard=source.slice(source.indexOf('function guard(log) {'),source.indexOf('mkdirSync(dir,'));
const good="'a' depends on axioms: [propext]\n'b' does not depend on any axioms\n",expected={pins:{a:['propext'],b:[]}};
const check=log=>{splitBatchReports(log,[{names:['a','b']}]);return runInNewContext(guard+'\nguard(log)',{expected,log});};assert.equal(check(good),2);
for(const text of [good.split('\n')[0],good+good,good.trim().split('\n').reverse().join('\n'),good.replace('propext','BAD'),good+'error: test'])assert.throws(()=>check(text));
console.log(JSON.stringify({status:'pass',host_only:true,not_authentication_or_Lean:true,production_driver_unchanged:true,exact_stable_inputs_keys_order:true,exact_same_manifest_interleaving:true,rows},null,2));
