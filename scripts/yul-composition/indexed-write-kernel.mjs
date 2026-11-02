import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {fileURLToPath} from 'node:url';
import {resolve} from 'node:path';
export const ROOT=fileURLToPath(new URL('../../',import.meta.url));
export const MODULE='Solidity/Yul/Composition/IndexedWritePhysical.lean';
export const EXPECTED_HASH="fb3d83af7168cdcc18fbb89fca14280beae02def4f59ad50b4ebfe502a7e22af";
export const THEOREMS=["run_actual", "run_reconstructed", "run_fields", "outer_revert", "prepared_frame", "run_memOK", "prepared_some", "witness_reconstructed", "witness_rollback", "witness_current_frame", "witness_heap_log", "witness_actual_bool", "witness_journals", "witness_aliases", "wrong_slot", "wrong_owner", "lost_raw_byte", "lost_padding", "wrong_tail", "full_topic", "wrong_topic", "static_emit_pending", "late_mark_keeps_write", "other_slot_actual", "other_owner_actual", "stale_encoding_actual", "wrong_raw_reconstruction", "static_write_refused", "static_emit_outer_revert", "late_mark_distinct", "inhabited_rollback"];
const sha=x=>createHash('sha256').update(x).digest('hex');
const NS='Solidity.Yul.Composition.IndexedWritePhysical.';
const PRIVATE_HEAD="621cb8fa4eb7de45961d26dac243719bde1599c3";
const PRODUCERS={"/workspace/vy5-dependencies-20261101/Solidity/Yul/World/IndexedEmitPort.lean": "be51ebec15a50b6c3402e64f484d54afb51044752f8f98055009a30a7afb65a0", "/workspace/vy5-dependencies-20261101/Solidity/Yul/World/ScalarLocalEmit.lean": "bf9545486e39466a58020f4b1284827dfb3e784565e4a2c4717591dc65b2db14", "/workspace/vy5-dependencies-20261101/Solidity/Yul/World/IndexedEmitHeap.lean": "41079e0f192e04a70f220d2d1c2f862a7e7b681778c97db9d3e18832aa00270e", "/workspace/vy5-dependencies-20261101/Solidity/Yul/World/IndexedEmitMemory.lean": "aa91b089a89c93a285d928de1cecf2828cc9e3d7ec5c0214858a530567baea8c"};
const PRIVATE_MODULE="/workspace/vy5-dependencies-20261101/Solidity/Yul/Composition/IndexedWritePhysical.lean";
const INPUTS='tests/yul-composition/indexed-write-inputs.json';
const INPUTS_HASH="5581e8525411c168f9d29b73ed6e2581f7ae117d5afb33bcf05ea49408df4bef";
const KERNEL_RECEIPT={"log": "/workspace/vy5-composition/evidence/indexed-write-20261102-joint-reviewed.log", "sha256": "03897c3aeca26e2f38d19cf93123e31599f6991e1f1a418838c5e763e9b22483", "exit": "/workspace/vy5-composition/evidence/indexed-write-20261102-joint-reviewed.exit", "resources": "/workspace/vy5-composition/evidence/indexed-write-20261102-joint-reviewed.resources.json", "resourcesSha256": "a28f29e5fdc5eb066324a3f32d45d8dab76a539074a84a7222e19bae14aedfb2"};
const PRIVATE_ROOT='/workspace/vy5-dependencies-20261101/';
const PROVENANCE='/workspace/vy5-composition/indexed-write-20261102/producer-provenance.json';
const read=path=>readFileSync(path);
/** Checks actual raw kernel receipts and ledger binding. It executes no EVM,
 * trusts no model outcome, and does not promote component laws to full coverage. */
export function validateIndexedWriteEvidence(report,readEvidence=read,readOwn=p=>readFileSync(resolve(ROOT,p))){
 assert.equal(report.schema,1);assert.equal(report.kind,'actual private kernel component');
 assert.equal(report.module,MODULE);assert.equal(report.moduleSha256,EXPECTED_HASH);
 assert.equal(report.privateHead,PRIVATE_HEAD);assert.equal(report.fullProofGate,'pending');
 assert.equal(report.nativeComparisons,0);assert.equal(report.finiteSourceCases,0);
 assert.deepEqual(report.theorems,THEOREMS);
 const moduleBytes=readOwn(MODULE);assert.equal(sha(moduleBytes),EXPECTED_HASH);
 assert.deepEqual([...String(moduleBytes).matchAll(/^theorem (\w+)/gm)].map(m=>m[1]),THEOREMS);
 const ledger=JSON.parse(readOwn('tests/yul-composition/indexed-write-ledger.json'));
 assert.equal(ledger.moduleSha256,EXPECTED_HASH);assert.deepEqual(ledger.theorems,THEOREMS);
 for(const k of ['fullProofGate','original24','sixGeneralCombinations'])assert.equal(ledger[k],'pending');
 assert.equal(ledger.nativeComparisons,0);assert.equal(ledger.finiteSourceCases,0);
 const parent=JSON.parse(readOwn('tests/yul-composition/ledger.json'));
 assert.equal(parent.indexedWriteEvidence,'tests/yul-composition/indexed-write-ledger.json');
 assert.equal(parent.obligations.length,24);assert.equal(parent.combinations.length,6);
 for(const o of [...parent.obligations,...parent.combinations]){assert.equal(o.status,'pending');assert.equal(o.proof,null);}
 const inputBytes=readOwn(INPUTS);assert.equal(sha(inputBytes),INPUTS_HASH);
 const inputs=JSON.parse(inputBytes);assert.equal(inputs.privateHead,PRIVATE_HEAD);assert.equal(inputs.module,MODULE);
 assert.equal(inputs.producerHead,'5a4678a0733702d5b74abffce9c7c6a2c3e45c28');
 assert.equal(sha(readEvidence(PROVENANCE)),inputs.producerProvenanceSha256);
 assert.equal(Object.keys(inputs.producerClosure).length,198);
 assert.equal(Object.keys(inputs.dependencyClosure).length,257);
 for(const [path,expected] of Object.entries(inputs.dependencyClosure))assert.equal(sha(readEvidence(PRIVATE_ROOT+path)),expected,path);
 for(const [path,expected] of Object.entries(inputs.producerClosure))assert.equal(inputs.dependencyClosure[path],expected,path);
 assert.deepEqual(report.producerHashes,PRODUCERS);assert.equal(report.privateModule,PRIVATE_MODULE);assert.equal(sha(readEvidence(PRIVATE_MODULE)),EXPECTED_HASH);
 for(const [path,expected] of Object.entries(report.producerHashes))assert.equal(sha(readEvidence(path)),expected);
 assert.equal(Object.keys(report.producerHashes).length,4);
 assert.deepEqual(report.kernel,KERNEL_RECEIPT);
 const log=String(readEvidence(report.kernel.log));assert.equal(sha(log),report.kernel.sha256);
 assert.equal(String(readEvidence(report.kernel.exit)).trim(),'0');
 const resourceBytes=readEvidence(report.kernel.resources);assert.equal(sha(resourceBytes),report.kernel.resourcesSha256);
 const resources=JSON.parse(resourceBytes);assert.equal(resources.exit,0);assert.equal(resources.stop,null);
 assert.equal(resources.memory,12*1024**3);assert.equal(resources.memorySwap,resources.memory);
 assert.ok(resources.minimumAvailableBytes>=4*1024**3);assert.ok(resources.peakSampledRSSBytes<resources.memory);
 const command=resources.command.at(-1);for(const required of ['lake build Solidity.KeySort','./run-lean.sh','lean -j1','check-trust.mjs <','check-automatic.mjs --strict'])assert.ok(command.includes(required));
 assert.match(log,/^Lean \(version 4\.24\.0,[^\n]*797c613[^\n]*\nLake version 5\.0\.0-src\+797c613[^\n]*\nBuild completed successfully \(2 jobs\)\./);
 assert.match(log,/Build completed successfully \(1300 jobs\)\./);assert.match(log,/Build completed successfully \(262 jobs\)\./);
 assert.match(log,/1315 reachable, 0 orphaned, 0 not allowed/);assert.match(log,/trust: 1330 sources, 252 inventoried implementation\/recovery sites, 0 findings/);
 const facts=validateScopedIndexedWriteAxioms(log);
 return {kernelComponent:'pass',facts:facts.length,fullProofGate:'pending',nativeComparisons:0};
}

export function validateScopedIndexedWriteAxioms(log){
 const facts=[];
 for(const m of log.matchAll(/'Solidity\.Yul\.Composition\.IndexedWritePhysical\.(\w+)' depends on axioms: \[([^\]]*)\]/g)){
  assert.ok(THEOREMS.includes(m[1]));assert.ok(!facts.includes(m[1]));facts.push(m[1]);
  for(const ax of m[2].split(',').map(x=>x.trim()).filter(Boolean))assert.ok(['propext','Classical.choice','Quot.sound'].includes(ax),ax);
 }
 for(const m of log.matchAll(/'Solidity\.Yul\.Composition\.IndexedWritePhysical\.(\w+)' does not depend on any axioms/g)){assert.ok(THEOREMS.includes(m[1]));assert.ok(!facts.includes(m[1]));facts.push(m[1]);}
 assert.deepEqual([...facts].sort(),[...THEOREMS].sort());
 return facts;
}
