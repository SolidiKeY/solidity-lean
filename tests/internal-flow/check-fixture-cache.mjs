#!/usr/bin/env node
// No Lean: exercise fail-closed cache mutations and the actual report parser.
import {readFileSync,writeFileSync,existsSync,unlinkSync,mkdirSync} from "node:fs";
import {spawnSync} from "node:child_process";
import {runInNewContext} from "node:vm";
import assert from "node:assert/strict";
const out=process.argv[2];
assert(out?.startsWith("/"));
const dir=".lake/build/lib/lean/tests/internal-flow", name="PublishedMemoryCalls";
const manifest=`${dir}/${name}.v12-cache.json`, object=`${dir}/${name}.olean`;
const original=readFileSync(manifest), binary=readFileSync(object);
const saved=JSON.parse(original), registry=JSON.parse(readFileSync("tests/internal-flow/fixture-axiom-pins.json","utf8"));
assert.equal(Object.keys(registry.TupleMemoryCalls.pins).length,85);
assert(Object.keys(saved.inputs).some(p=>p.endsWith("/Init/Prelude.olean")));
assert(Object.keys(saved.inputs).some(p=>p.endsWith("/libleanshared.so")));
assert("lakefile.toml" in saved.inputs);
const bin=`${out}/cache-controls-bin`;mkdirSync(bin,{recursive:true});
const marker=`${out}/UNEXPECTED_LEAN_INVOCATION`;
assert(!existsSync(marker));
writeFileSync(`${bin}/lake`,`#!/bin/sh\necho unexpected > "${marker}"\nexit 97\n`,{mode:0o755});
// Exercise the sentinel itself: malformed literal-backslash newlines fail here.
assert.equal(spawnSync(`${bin}/lake`).status,97);
assert(existsSync(marker));unlinkSync(marker);
const harness=readFileSync(`${out}/cached-${name}-import.lean`,"utf8");
assert(!harness.includes(String.fromCharCode(92)+"n"));
assert.equal(harness.trimEnd().split(String.fromCharCode(10)).length,28);
assert(harness.startsWith(`import tests.«internal-flow».${name}`+String.fromCharCode(10)));
const cases=[];
function reject(tag,mutate,reason) {
  try {
    writeFileSync(manifest,original);writeFileSync(object,binary);
    mutate();
    const result=spawnSync(process.execPath,["tests/internal-flow/fixture-cache.mjs","check",`tests/internal-flow/${name}.lean`,out],
      {encoding:"utf8",env:{...process.env,PATH:bin+":"+process.env.PATH}});
    writeFileSync(`${out}/cache-reject-${tag}.log`,(result.stdout??"")+(result.stderr??""));
    assert.notEqual(result.status,0);assert.match(result.stderr,reason);assert(!existsSync(marker));
    cases.push({case:tag,status:result.status,rejected_before_Lean:true});
  } finally {writeFileSync(manifest,original);writeFileSync(object,binary);}
}
reject("missing",()=>unlinkSync(manifest),/missing checked fixture cache/);
reject("key",()=>writeFileSync(manifest,JSON.stringify({...saved,key:"wrong"})),/stale or altered/);
reject("source-binding",()=>writeFileSync(manifest,JSON.stringify({...saved,inputs:{...saved.inputs,[`tests/internal-flow/${name}.lean`]:"wrong"}})),/stale or altered/);
reject("object",()=>writeFileSync(object,Buffer.concat([binary,Buffer.from("altered")])),/stale or altered/);
assert.deepEqual(readFileSync(manifest),original);assert.deepEqual(readFileSync(object),binary);
const source=readFileSync("tests/internal-flow/fixture-cache.mjs","utf8");
const guard=source.slice(source.indexOf("function guard(log) {"),source.indexOf("mkdirSync(dir,"));
const expected=registry[name], log=readFileSync(`${out}/prepared-${name}.log`,"utf8");
const evaluate=text=>runInNewContext(guard+"\nguard(log)",{expected,log:text});
assert.equal(evaluate(log),27);
const report=log.match(/\x27[^\x27]+\x27 (?:depends on axioms:\s*\[[^\]]*\]|does not depend on any axioms)/)[0];
for(const [tag,bad] of [["missing-report",log.replace(report,"")],["duplicate-report",log+"\n"+report],["wrong-axiom",log.replace("propext","BAD_AXIOM")],["diagnostic",log+"\nerror: injected"]]) {
  assert.throws(()=>evaluate(bad));cases.push({case:tag,rejected:true});
}
console.log(JSON.stringify({status:"pass",no_Lean:true,cases},null,2));
