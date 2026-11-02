#!/usr/bin/env node
// No Lean. Extract the ACTUAL old/new key bodies, with controlled filesystem
// fixtures. Neither these test manifests nor timings authenticate Lean objects.
import * as fs from "node:fs";
import {createHash} from "node:crypto";
import {runInNewContext} from "node:vm";
import assert from "node:assert/strict";
import {imports,splitBatchReports} from "./fixture-cache.mjs";
const baseline=fs.readFileSync(process.argv[2],"utf8");
const changed=fs.readFileSync("tests/internal-flow/fixture-cache.mjs","utf8");
const digest=b=>createHash("sha256").update(b).digest("hex");
export const keyBody=s=>s.slice(s.indexOf("function key() {"),s.indexOf("function guard(log) {"));
export function factory(source,file,registry,read,exists,sharedToolchain) {
  const context={file,registry,readFileSync:read,existsSync:exists,sharedToolchain,
    toolchainInputs:()=>{throw Error("test must supply explicit toolchain inputs")},
    pinsFile:"tests/internal-flow/fixture-axiom-pins.json",expected:registry[file.split("/").at(-1).slice(0,-5)],
    dir:".lake/build/lib/lean/tests/internal-flow",imports,createHash,hash:p=>digest(read(p))};
  const body=keyBody(source).replace('"tests/internal-flow/fixture-cache.mjs","lean-toolchain"','"tests/internal-flow/fixture-cache.mjs","tests/internal-flow/exact-byte-digest.mjs","lean-toolchain"');
  context.freshObjectDigest=p=>digest(read(p));
  return runInNewContext(body+"\nkey",context);
}
const file="tests/internal-flow/Main.lean", dep="tests/internal-flow/Dep.lean", leaf="Solidity/Leaf.lean";
const registry={Main:{guard:"main-guard.py",pins:{a:["propext"],b:[]}},Dep:{guard:"dep-guard.py",pins:{}}};
const objects=p=>".lake/build/lib/lean/"+p.slice(0,-5)+".olean";
const manifest=".lake/build/lib/lean/tests/internal-flow/Dep.v12-cache.json";
const initial=new Map(Object.entries({[file]:'import tests.«internal-flow».Dep\n',[dep]:'import Solidity.Leaf\n',[leaf]:'import Init.Prelude\n-- raw byte test\n',
 [objects(dep)]:'dep object',[objects(leaf)]:'leaf object',"main-guard.py":"root guard","dep-guard.py":"dep guard",
 "tests/internal-flow/fixture-axiom-pins.json":"registry", "tests/internal-flow/fixture-cache.mjs":"IDENTICAL DRIVER INPUT FOR ALGORITHM COMPARISON",
 "tests/internal-flow/exact-byte-digest.mjs":"EXACT TEST HELPER INPUT", "lean-toolchain":"lean4", "lakefile.toml":"config"}).map(([p,b])=>[p,Buffer.from(b)]));
// Invalid UTF8 inside a comment proves hashing uses original bytes, not a
// decoded/re-encoded string. The existing parser consumes decoded exact text.
initial.set(leaf,Buffer.concat([initial.get(leaf),Buffer.from([47,45,255,254,45,47])]));
const tc={"compiler-binary":"compiler","toolchain/Init/Prelude.olean":"toolchain"};
function harness(source,files=new Map(initial),root=file,onRead=null) {
  const reads=[];
  const read=(p,encoding)=>{if(!files.has(p))throw Error("ENOENT "+p);const b=Buffer.from(files.get(p));reads.push({p,hex:b.toString("hex")});onRead?.(p,files);return encoding?b.toString(encoding):b;};
  return {files,reads,key:factory(source,root,registry,read,p=>files.has(p),tc)};
}
function prepared(source) {
 const h=harness(source, new Map(initial),dep);const saved=h.key();
 h.files.set(manifest,Buffer.from(JSON.stringify({...saved,object_sha256:digest(h.files.get(objects(dep)))})));
 return h.files;
}
const data=prepared(baseline), old=harness(baseline,new Map(data)), fresh=harness(changed,new Map(data));
const before=old.key(), after=fresh.key();
assert.equal(JSON.stringify(after),JSON.stringify(before),"EXACT serialized input order/key equality");
assert.equal(after.inputs[leaf],digest(data.get(leaf)));
for(const p of [file,dep,leaf]) {
 assert.equal(old.reads.filter(x=>x.p===p).length,2);
 assert.equal(fresh.reads.filter(x=>x.p===p).length,1);
 assert.equal(fresh.reads.find(x=>x.p===p).hex,data.get(p).toString("hex"));
}
const cases=[];
for(const p of [file,dep,leaf,objects(dep),objects(leaf),"main-guard.py","dep-guard.py",manifest,"lean-toolchain","lakefile.toml","tests/internal-flow/fixture-axiom-pins.json","tests/internal-flow/fixture-cache.mjs","tests/internal-flow/exact-byte-digest.mjs"]) {
 const h=harness(changed,new Map(data));const saved=h.key();
 h.files.set(p,Buffer.concat([h.files.get(p),Buffer.from("\nchanged")]));
 let rejected=false;try{rejected=h.key().key!==saved.key}catch{rejected=true}
 assert(rejected,"mutation BETWEEN key calls accepted: "+p);cases.push({path:p,rejected:true});
}
for(const p of [dep,objects(dep),manifest]) {
 const h=harness(changed,new Map(data));h.files.delete(p);assert.throws(()=>h.key());cases.push({missing:p,rejected:true});
}
// Changed imports must rebuild the actual closure on the next key call,
// rather than reuse a file-name or hash cache from the first traversal.
const importsChanged=harness(changed,new Map(data));const prior=importsChanged.key();
importsChanged.files.set(file,Buffer.from('import tests.«internal-flow».Dep\nimport Solidity.New\n'));
importsChanged.files.set("Solidity/New.lean",Buffer.from("import Init.Prelude\n"));
importsChanged.files.set(objects("Solidity/New.lean"),Buffer.from("new object"));
const rebuilt=importsChanged.key();assert("Solidity/New.lean" in rebuilt.inputs);assert.notEqual(rebuilt.key,prior.key);
cases.push({changed_import_closure:true,rejected_old_key:true});
for(const field of ["key","object_sha256","inputs"]) {
 const altered=new Map(data),receipt=JSON.parse(altered.get(manifest));
 if(field==="inputs")receipt.inputs["lean-toolchain"]="altered";else receipt[field]="altered";
 altered.set(manifest,Buffer.from(JSON.stringify(receipt)));
 assert.throws(()=>harness(changed,altered).key(),/stale or altered/);cases.push({manifest_field:field,rejected:true});
}
// A mutation immediately AFTER the source read cannot make parsing/hash use
// different bytes. It MUST be observed by the next independent key invocation.
const h=harness(changed,new Map(data),file,(p,files)=>{if(p===file)files.set(p,Buffer.from('import tests.«internal-flow».Dep\n-- changed after read\n'))});
const during=h.key();assert.equal(during.inputs[file],digest(data.get(file)));
assert.notEqual(h.key().key,during.key);
const guard=changed.slice(changed.indexOf("function guard(log) {"),changed.indexOf("mkdirSync(dir,"));
const good="'a' depends on axioms: [propext]\n'b' does not depend on any axioms\n";
const groups=[{names:["a","b"]}];
const validate=log=>{splitBatchReports(log,groups);return runInNewContext(guard+"\nguard(log)",{expected:registry.Main,log});};
assert.equal(validate(good),2);
for(const [name,log]of Object.entries({missing:good.split("\n")[0],reordered:good.trim().split("\n").reverse().join("\n"),duplicate:good+good,wrong:good.replace("propext","sorryAx"),error:good+"error: test"})) {assert.throws(()=>validate(log));cases.push({report:name,rejected:true});}
console.log(JSON.stringify({status:"pass",no_Lean:true,exact_serialized_inputs_keys_and_order:true,source_reads_per_key:{before:2,after:1},new_helper_dimension_normalized_explicitly:true,raw_bytes:true,mutation_after_read_coherent_next_call_fresh:true,cases},null,2));
