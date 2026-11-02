#!/usr/bin/env node
// No Lean; affected key work only, never an aggregate/proof certificate.
// Old/new ACTUAL key implementations consume identical real source/object/
// guard/config/toolchain bytes. Dependency receipts here are synthetic test
// values, not authenticated production manifests, and are never written there.
import * as fs from "node:fs";
import {createHash} from "node:crypto";
import {runInNewContext} from "node:vm";
import assert from "node:assert/strict";
import {performance} from "node:perf_hooks";
import {imports} from "./fixture-cache.mjs";
import {factory} from "./check-key-source-bytes.mjs";
const baseline=fs.readFileSync(process.argv[2],"utf8"),changed=fs.readFileSync("tests/internal-flow/fixture-cache.mjs","utf8");
const output=process.argv[3];assert(output?.startsWith("/"));
const registry=JSON.parse(fs.readFileSync("tests/internal-flow/fixture-axiom-pins.json","utf8"));
const toolBody=changed.slice(changed.indexOf("function toolchainInputs() {"),changed.indexOf("// Production traversal"));
const digest=b=>createHash("sha256").update(b).digest("hex");
const tool=runInNewContext(toolBody+"\ntoolchainInputs",{...fs,process,hash:p=>digest(fs.readFileSync(p))});
const before=tool(),overrides=new Map(),ordered=[],seen=new Set();
function visit(name) {
 if(seen.has(name))return;seen.add(name);
 for(const mod of imports(fs.readFileSync(`tests/internal-flow/${name}.lean`,"utf8"))) {
  const m=/^tests\.«internal-flow»\.([A-Za-z][A-Za-z0-9]*)$/.exec(mod);if(m)visit(m[1]);
 }
 ordered.push(name);
}
Object.keys(registry).sort().forEach(visit);
assert.equal(ordered.length,27);assert.equal(Object.values(registry).reduce((n,r)=>n+Object.keys(r.pins).length,0),739);
function harness(source,name,metrics=null) {
 const read=(path,encoding)=>{
  const start=performance.now();
  // Preserve the production read mode: legacy parsing requests UTF8 directly,
  // while the repaired parser deliberately reads a Buffer for parse+hash.
  const value=overrides.has(path)?(encoding?overrides.get(path).toString(encoding):Buffer.from(overrides.get(path))):fs.readFileSync(path,encoding);
  const elapsed=performance.now()-start;
  const byteLength=Buffer.isBuffer(value)?value.length:Buffer.byteLength(value,encoding);
  const source=path.endsWith(".lean")&&!path.endsWith("lakefile.lean");
  if(metrics) {metrics[source?"source_reads":"other_reads"]++;metrics[source?"source_bytes":"other_bytes"]+=byteLength;metrics[source?"source_read_ms":"other_read_ms"]+=elapsed;}
  return value;
 };
 return factory(source,`tests/internal-flow/${name}.lean`,registry,read,p=>overrides.has(p)||fs.existsSync(p),before);
}
const reference=new Map();
for(const name of ordered) {
 const key=harness(baseline,name)();reference.set(name,JSON.stringify(key));
 const object=`.lake/build/lib/lean/tests/internal-flow/${name}.olean`;
 overrides.set(`.lake/build/lib/lean/tests/internal-flow/${name}.v12-cache.json`,Buffer.from(JSON.stringify({...key,object_sha256:digest(fs.readFileSync(object))})));
 assert.equal(JSON.stringify(harness(changed,name)()),reference.get(name));
}
const results=[];
for(let round=0;round<3;round++)for(const mode of round%2?["after","before"]:["before","after"]) {
 const m={round,mode,source_reads:0,source_bytes:0,other_reads:0,other_bytes:0,source_read_ms:0,other_read_ms:0};
 const start=performance.now();
 for(const name of ordered)assert.equal(JSON.stringify(harness(mode==="before"?baseline:changed,name,m)()),reference.get(name));
 m.elapsed_ms=performance.now()-start;results.push(m);
}
assert.equal(JSON.stringify(tool()),JSON.stringify(before));
const median=mode=>results.filter(r=>r.mode===mode).map(r=>r.elapsed_ms).sort((a,b)=>a-b)[1];
const report={no_Lean:true,not_authentication_or_aggregate:true,fixture_count:27,reports:739,ordered_fixture_names:ordered,
 source_of_inputs:"actual unchanged source/object/guard/config bytes and freshly hashed complete real toolchain; synthetic in-memory dependency receipts only for comparison, never production",toolchain_entries:Object.keys(before).length,
 actual_complete_toolchain_before_after_equal:true,exact_complete_key_input_order_equal:true,
 results,before_median_ms:median("before"),after_median_ms:median("after"),measured_improvement:median("after")<median("before"),
 kernel_stage:"not run or timed here; existing authenticated preparation/gate checks remain required, no kernel speedup claimed"};
fs.writeFileSync(output,JSON.stringify(report,null,2)+"\n");console.log(JSON.stringify(report));
