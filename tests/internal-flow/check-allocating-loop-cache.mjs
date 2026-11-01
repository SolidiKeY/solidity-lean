#!/usr/bin/env node
import assert from "node:assert/strict";
import {splitBatchReports} from "./fixture-cache.mjs";
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
const groups=files.map(file=>({names:Object.keys(registry[file.split("/").at(-1).slice(0,-5)].pins).sort()}));
const reports=groups.flatMap(group=>group.names.map(name=>`'${name}' depends on axioms: [propext]`));
const positive=splitBatchReports(reports.join("\n"),groups);
assert.equal(positive.length,files.length);
assert.equal(positive.reduce((n,s)=>n+[...s.matchAll(/depends on axioms:/g)].length,0),reports.length);
const splitControls=[];
for(const [tag,bad] of [["missing",reports.slice(1).join("\n")],["duplicate",[reports[0],...reports].join("\n")],
 ["reordered",[reports[1],reports[0],...reports.slice(2)].join("\n")],["extra",[...reports,"'Unexpected.extra' depends on axioms: []"].join("\n")],
 ["error",reports.join("\n")+"\nerror: synthetic batch control"],
 ["wrong-name",["'Unexpected.wrong' depends on axioms: []",...reports.slice(1)].join("\n")]]) {
 assert.throws(()=>splitBatchReports(bad,groups));splitControls.push({case:tag,rejected:true,synthetic_no_Lean:true});
}
console.log(JSON.stringify({status:"pass",no_Lean:true,fixtures:files,cases,complete_report_count:reports.length,splitControls},null,2));
