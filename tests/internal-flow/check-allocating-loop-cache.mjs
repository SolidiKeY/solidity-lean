#!/usr/bin/env node
import assert from "node:assert/strict";
import {readFileSync,writeFileSync,existsSync,unlinkSync,mkdirSync} from "node:fs";
import {spawnSync} from "node:child_process";
const out=process.argv[2];assert(out?.startsWith("/"));
const registry=JSON.parse(readFileSync("tests/internal-flow/fixture-axiom-pins.json","utf8"));
const files=Object.keys(registry).map(n=>`tests/internal-flow/${n}.lean`).sort();
const bin=`${out}/batch-controls-bin`;mkdirSync(bin,{recursive:true});
const marker=`${out}/UNEXPECTED_BATCH_LEAN`;assert(!existsSync(marker));
writeFileSync(`${bin}/lake`,`#!/bin/sh\necho unexpected > "${marker}"\nexit 97\n`,{mode:0o755});
assert.equal(spawnSync(`${bin}/lake`).status,97);assert(existsSync(marker));unlinkSync(marker);
const cases=[];
for(const [tag,bad] of [["missing",files.slice(1)],["duplicate",[files[0],...files]],["wrong-order",[...files].reverse()],["unregistered",[...files,"tests/internal-flow/Unknown.lean"]]]) {
 const result=spawnSync(process.execPath,["tests/internal-flow/fixture-cache.mjs","batch",out,...bad],{encoding:"utf8",env:{...process.env,PATH:bin+":"+process.env.PATH}});
 writeFileSync(`${out}/batch-reject-${tag}.log`,(result.stdout??"")+(result.stderr??""));
 assert.notEqual(result.status,0);assert.match(result.stderr,/EVERY registered fixture exactly once/);assert(!existsSync(marker));
 cases.push({case:tag,exit:result.status,rejected_before_Lean:true});
}
console.log(JSON.stringify({status:"pass",no_Lean:true,fixtures:files,cases},null,2));
