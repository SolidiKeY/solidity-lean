import test from 'node:test';
import assert from 'node:assert/strict';
import fs,{readFileSync} from 'node:fs';
import {syncBuiltinESMExports} from 'node:module';
import {join,resolve} from 'node:path';
import {verifyRuntimeInputs,validateRuntimeModel,validateRuntimeReport} from './runtime-block-source.mjs';
const DIR='/workspace/vy5-composition/runtime-block-20261102/readback-v1',r=JSON.parse(readFileSync(join(DIR,'report.json')));
test('actual28laws/12Sourcecases/runtime declaration andABI controls, fullhistorical24calls separate from ZEROnew native comparisons',()=>{
 validateRuntimeReport(r,DIR);const l=JSON.parse(readFileSync('tests/yul-composition/runtime-block-ledger.json'));assert.equal(l.facts.length,28);assert.equal(l.obligations.length,24);assert.equal(l.combinations.length,6);assert.equal(l.fullCoverage,false);assert.equal(r.model.cases.length,12);assert.deepEqual(r.model.declared.refs.map(v=>v.logicalIndex),[1,1,0]);assert.equal(r.rows.length,0);assert.equal(r.nativeComparisons.length,0);assert.equal(r.historicalValidation.orderedCalls,24);assert.equal(r.nativeExecution,'historical-replay-only');
});
for(const key of Object.keys(r.model))test('missing/malformed model '+key,()=>{const m=structuredClone(r.model);delete m[key];assert.throws(()=>validateRuntimeModel(m));const n=structuredClone(r.model);n[key]=null;assert.throws(()=>validateRuntimeModel(n));});
const mutations={
 'logical index called physical':m=>m.addressDomain='evm-address',
 'runtime declaration missing':m=>m.declared=null,
 'initializer aliases wrong same-type local':m=>m.declared.refs[0].logicalIndex=0,
 'old alias overwritten':m=>m.declared.refs[2].logicalIndex=1,
 'declaration ref order':m=>m.declared.refs.reverse(),
 'declaration payload wrong':m=>m.declared.heap.bytes=[170,187],
 'low fuel incorrectly rethrows':m=>m.cases[0].result={tag:'revert',bytes:[222,173]},
 'fuel3 incorrectly succeeds':m=>m.cases[1].result={tag:'success',bytes:[]},
 'fuel4 loses full bytes':m=>m.cases[2].result.bytes=[170,187],
 'fuel32 different result':m=>m.cases[3].result.bytes.pop(),
 'empty rethrow became success':m=>m.cases[4].result.tag='success',
 'panic tail corrupted':m=>m.cases[5].result.bytes[35]=17,
 'success forced through rethrow':m=>m.cases[6].result={tag:'revert',bytes:[190,239]},
 'timeout swallowed':m=>m.cases[7].result={tag:'success',bytes:[]},
 'stuck changed to revert':m=>m.cases[8].result={tag:'revert',bytes:[]},
 'explicit ABI revert falsely length-rejected':m=>m.cases[9].result.bytes=[],
 'short successful ABI return falsely retainsDEAD':m=>m.cases[10].result.bytes=[222,173],
 'short return did not allocate empty catch':m=>m.cases[10].after.object=null,
 'error state prefix rolled back':m=>m.cases[11].after.logs.shift(),
 'error state wrong message':m=>m.cases[11].result.reason='other',
 'caller scope not restored':m=>m.cases[2].restored.logicalIndex=1,
 'dirty raw caller reset':m=>m.cases[2].after.raw[3]='1',
 'dirty bool cleaned':m=>m.cases[2].after.raw[0]='1',
 'caller nonword alias lost':m=>m.cases[2].after.alias=null,
 'new heap missing with same bytes':m=>m.cases[2].after.object=null,
 'timeout pretends no allocation':m=>m.cases[0].after.next=1,
 'success incorrectly allocates':m=>m.cases[6].after.next=2,
 'wrong alias falsely normalized toDEAD':m=>m.wrongAlias.result.bytes=[222,173],
 'wrong alias changed new allocated object':m=>m.wrongAlias.after.object.bytes=[170,187],
 'raw clean resumption allowed':m=>m.cases[2].after.clean=true,
 'case ordering':m=>m.cases.reverse()
};
for(const[name,change]of Object.entries(mutations))test(name,()=>{const m=structuredClone(r.model);change(m);assert.throws(()=>validateRuntimeModel(m));});
for(const[name,change]of Object.entries({
 'false freshEVM':r=>r.nativeExecution='fresh',
 'false fullproof':r=>r.fullProofGate='pass',
 'invented native rethrow comparison':r=>r.nativeComparisons=[{status:'match'}],
 'old caughtcall relabelled new path':r=>r.rows=[{status:'match'}],
 'lost historical full24validation':r=>r.historicalValidation.orderedCalls=16,
 'false historical role':r=>r.historicalValidation.role='rethrow-source adequacy',
 'stale parent hash':r=>r.referenceSha256='0'.repeat(64),
 'stale own source':r=>r.inputHashes['Solidity/Yul/Composition/RuntimeBlockPhysical.lean']='0'.repeat(64),
 'stale runner':r=>r.runnerSha256='0'.repeat(64)
}))test(name,()=>{const x=structuredClone(r);change(x);assert.throws(()=>validateRuntimeReport(x,DIR));});
for(const file of ['Solidity/Source/Types.lean','Solidity/Source/Value.lean','Solidity/Source/Elaborated.lean','Solidity/Source/State.lean','Solidity/Source/Machine.lean','Solidity/Source/Eval.lean','Solidity/Source/Resolved.lean','Solidity/Source/Hoare.lean','Solidity/Yul/Composition/RuntimeBlockPhysical.lean','Solidity/Yul/Composition/ScopeCatchPhysical.lean','tests/yul-composition/RuntimeBlockDriver.lean','tests/yul-composition/runtime-block-expectations.json','tests/yul-composition/runtime-block-ledger.json'])test('actual private/main body drift '+file,()=>{
 const original=fs.readFileSync,paths=new Set([resolve(file),'/workspace/vy5-dependencies-20261101/'+file]);
 try{fs.readFileSync=function(path,...args){const v=original.call(this,path,...args);return paths.has(String(path))?(typeof v==='string'?v+'\n':Buffer.concat([v,Buffer.from('\n')])):v;};syncBuiltinESMExports();assert.throws(()=>verifyRuntimeInputs('/workspace/vy5-dependencies-20261101'));}finally{fs.readFileSync=original;syncBuiltinESMExports();}
});
for(const file of ['lean.stdout','lean.stderr','lean.execution.json'])test('actual execution drift '+file,()=>{
 const original=fs.readFileSync;
 try{fs.readFileSync=function(path,...args){return String(path)===join(DIR,file)?'{}':original.call(this,path,...args);};syncBuiltinESMExports();assert.throws(()=>validateRuntimeReport(r,DIR));}finally{fs.readFileSync=original;syncBuiltinESMExports();}
});
for(const target of ['/workspace/vy5-composition/rethrow-20261101/readback-v1/report.json','/workspace/vy5-composition/attempt-20261101/native-v2/report.json'])test('sealed full reference cannot drift '+target,()=>{
 const original=fs.readFileSync;
 try{fs.readFileSync=function(path,...args){return String(path)===target?Buffer.from('{}'):original.call(this,path,...args);};syncBuiltinESMExports();assert.throws(()=>validateRuntimeReport(r,DIR));}finally{fs.readFileSync=original;syncBuiltinESMExports();}
});
test('selected required rethrow catalog cannot disappear',()=>{
 const original=fs.readFileSync,target=resolve('tests/yul-composition/ledger.json'),root=JSON.parse(original(target));delete root.runtimeBlockEvidence;
 try{fs.readFileSync=function(path,...args){return String(path)===target?Buffer.from(JSON.stringify(root)):original.call(this,path,...args);};syncBuiltinESMExports();assert.throws(()=>validateRuntimeReport(r,DIR));}finally{fs.readFileSync=original;syncBuiltinESMExports();}
});

 test('original strict five native journal failures remain immutableFAIL',()=>{const path='/workspace/vy5-composition/native-rethrow-20261101/original-v3/report.json',original=fs.readFileSync;try{fs.readFileSync=function(file,...args){if(String(file)===path){const o=JSON.parse(original(file));o.validation='pass';return Buffer.from(JSON.stringify(o));}return original.call(this,file,...args);};syncBuiltinESMExports();assert.throws(()=>validateRuntimeReport(r,DIR));}finally{fs.readFileSync=original;syncBuiltinESMExports();}});
