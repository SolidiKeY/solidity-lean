#!/usr/bin/env node
// Readiness/tamper controls only. Actual kernel imports are a separate gate.
import assert from "node:assert/strict";
import {readFileSync,writeFileSync,existsSync,unlinkSync,mkdirSync} from "node:fs";
import {spawnSync} from "node:child_process";
const out=process.argv[2];assert(out?.startsWith("/"));
const dir=".lake/build/lib/lean/tests/internal-flow";
const manifest=`${dir}/CallLoopEndpoint.v12-cache.json`;
const saved=JSON.parse(readFileSync(manifest,"utf8"));
for(const dependency of ["CallLoopFacts","PublishedMemoryLoops"]) {
  assert(`tests/internal-flow/${dependency}.lean` in saved.inputs);
  assert(`${dir}/${dependency}.olean` in saved.inputs);
  assert(`${dir}/${dependency}.v12-cache.json` in saved.inputs);
}
const bin=`${out}/dependency-controls-bin`;mkdirSync(bin,{recursive:true});
const marker=`${out}/UNEXPECTED_DEPENDENCY_LEAN`;
assert(!existsSync(marker));
writeFileSync(`${bin}/lake`,`#!/bin/sh\necho unexpected > "${marker}"\nexit 97\n`,{mode:0o755});
assert.equal(spawnSync(`${bin}/lake`).status,97);assert(existsSync(marker));unlinkSync(marker);
const cases=[];
function reject(tag,path,mutate,reason) {
  const original=readFileSync(path);
  try {
    mutate(path,original);
    const result=spawnSync(process.execPath,["tests/internal-flow/fixture-cache.mjs","check","tests/internal-flow/CallLoopEndpoint.lean",out],
      {encoding:"utf8",env:{...process.env,PATH:bin+":"+process.env.PATH}});
    writeFileSync(`${out}/dependency-reject-${tag}.log`,(result.stdout??"")+(result.stderr??""));
    assert.notEqual(result.status,0);assert.match(result.stderr,reason);assert(!existsSync(marker));
    cases.push({case:tag,exit:result.status,rejected_before_Lean:true});
  } finally {writeFileSync(path,original);}
}
reject("missing-facts-provenance",`${dir}/CallLoopFacts.v12-cache.json`,p=>unlinkSync(p),/missing checked fixture dependency/);
reject("altered-facts-object",`${dir}/CallLoopFacts.olean`,(p,b)=>writeFileSync(p,Buffer.concat([b,Buffer.from("altered")])),/stale or altered checked fixture dependency/);
reject("altered-transitive-source","tests/internal-flow/PublishedMemoryLoops.lean",(p,b)=>writeFileSync(p,Buffer.concat([b,Buffer.from("\n-- tamper control\n")])),/stale or altered checked fixture dependency/);
reject("altered-dependency-binding",`${dir}/CallLoopFacts.v12-cache.json`,(p,b)=>{const x=JSON.parse(b);x.object_sha256="wrong";writeFileSync(p,JSON.stringify(x));},/stale or altered checked fixture dependency/);
reject("unregistered-import","tests/internal-flow/CallLoopEndpoint.lean",(p,b)=>writeFileSync(p,Buffer.concat([b,Buffer.from("\nimport tests.«internal-flow».NotRegistered\n")])),/unsupported fixture dependency/);
console.log(JSON.stringify({status:"pass",no_Lean:true,registered_transitive_dependencies:2,cases},null,2));
