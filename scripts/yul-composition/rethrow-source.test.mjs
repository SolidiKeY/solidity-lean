import test from 'node:test';
import assert from 'node:assert/strict';
import fs,{readFileSync} from 'node:fs';
import {syncBuiltinESMExports} from 'node:module';
import {join,resolve} from 'node:path';
import {verifyRethrowInputs,validateRethrowModel,validateRethrowReport} from './rethrow-source.mjs';
const DIR='/workspace/vy5-composition/rethrow-20261101/readback-v1',r=JSON.parse(readFileSync(join(DIR,'report.json')));
test('actual20laws/12composedcases/6controls, fullhistorical24calls separate from ZEROnew native comparisons',()=>{
 validateRethrowReport(r,DIR);const l=JSON.parse(readFileSync('tests/yul-composition/rethrow-component-ledger.json'));assert.equal(l.facts.length,20);assert.equal(l.obligations.length,24);assert.equal(l.combinations.length,6);assert.equal(l.fullCoverage,false);assert.equal(r.model.cases.length,12);assert.equal(r.model.controls.length,6);assert.equal(r.rows.length,0);assert.equal(r.nativeComparisons.length,0);assert.equal(r.historicalValidation.orderedCalls,24);assert.equal(r.nativeExecution,'historical-replay-only');
});
for(const key of Object.keys(r.model))test('missing/malformed model '+key,()=>{const m=structuredClone(r.model);delete m[key];assert.throws(()=>validateRethrowModel(m));const n=structuredClone(r.model);n[key]=null;assert.throws(()=>validateRethrowModel(n));});
const mutations={
 'logical index falsely physical':m=>m.addressDomain='evm-address',
 'fake compiler execution':m=>m.global='viaIR compiler',
 'lost captured fullbytes':m=>m.cases[1].capturedScope.bytes=[173,222],
 'wrong typed reference':m=>m.cases[1].capturedScope.ref.logicalIndex=0,
 'wrong returned local index order':m=>m.cases[1].capturedScope.inner.reverse(),
 'rethrow wrong same-length bytes':m=>m.cases[1].result.bytes=[170,187],
 'empty rethrow treated success':m=>m.cases[4].result={tag:'success',bytes:[]},
 'panic tail lost':m=>m.cases[7].result.bytes.pop(),
 'panic wrong fulltail':m=>m.cases[8].result.bytes[35]=17,
 'zero fuel incorrectly rethrows':m=>m.cases[0].result={tag:'revert',bytes:[222,173]},
 'fuel increased in receipt':m=>m.cases[0].fuel=1,
 'success incorrectly caught at0':m=>m.cases[9].result={tag:'timeout'},
 'prior timeout swallowed':m=>m.cases[10].result={tag:'success',bytes:[]},
 'prior stuck swallowed':m=>m.cases[11].result={tag:'revert',bytes:[]},
 'outer local not restored':m=>m.cases[1].restoredAfter.logicalIndex=1,
 'caller prefix wrong':m=>m.cases[1].restoredBefore.logicalIndex=1,
 'raw caller reset':m=>m.cases[1].after.raw[3]='1',
 'dirty bool cleaned':m=>m.cases[1].after.raw[0]='1',
 'post heap rollback wrongly inferred':m=>m.cases[1].after.next=1,
 'allocated bytes corrupted with same return':m=>m.cases[1].after.object.bytes=[173,222],
 'before heap reference missing':m=>m.cases[1].before.object=null,
 'old nonword alias overwritten':m=>m.cases[1].after.alias.bytes=[222,173],
 'logs silently rolled back':m=>m.cases[1].after.logs.pop(),
 'wrong index normalized to right result':m=>m.controls[2].result.bytes=[222,173],
 'wrong index input reset':m=>m.controls[2].inside.reverse(),
 'dangling pointer clamped':m=>m.controls[3].inside[0].logicalIndex=1,
 'dangling error becomes revert':m=>m.controls[3].result={tag:'revert',bytes:[]},
 'dangling0 dereferenced before timeout':m=>m.controls[1].result={tag:'stuck',reason:'dangling memory reference'},
 'control caller restoration lost':m=>m.controls[3].restored.logicalIndex=2,
 'control state changed despite same bytes':m=>m.controls[2].after.raw[3]='1794',
 'case ordering':m=>m.cases.reverse(),
 'control ordering':m=>m.controls.reverse()
};
for(const[name,change]of Object.entries(mutations))test(name,()=>{const m=structuredClone(r.model);change(m);assert.throws(()=>validateRethrowModel(m));});
for(const[name,change]of Object.entries({
 'false freshEVM':r=>r.nativeExecution='fresh',
 'false fullproof':r=>r.fullProofGate='pass',
 'invented native rethrow comparison':r=>r.nativeComparisons=[{status:'match'}],
 'old caughtcall relabelled new path':r=>r.rows=[{status:'match'}],
 'lost historical full24validation':r=>r.historicalValidation.orderedCalls=16,
 'false historical role':r=>r.historicalValidation.role='rethrow-source adequacy',
 'stale parent hash':r=>r.referenceSha256='0'.repeat(64),
 'stale own source':r=>r.inputHashes['Solidity/Yul/Composition/RethrowPhysical.lean']='0'.repeat(64),
 'stale runner':r=>r.runnerSha256='0'.repeat(64)
}))test(name,()=>{const x=structuredClone(r);change(x);assert.throws(()=>validateRethrowReport(x,DIR));});
for(const file of ['Solidity/Source/State.lean','Solidity/Source/Machine.lean','Solidity/Source/Eval.lean','Solidity/Source/Resolved.lean','Solidity/Source/Hoare.lean','Solidity/Yul/Composition/RethrowPhysical.lean','Solidity/Yul/Composition/ScopeCatchPhysical.lean','tests/yul-composition/RethrowDriver.lean','tests/yul-composition/rethrow-expectations.json','tests/yul-composition/rethrow-component-ledger.json'])test('actual private/main body drift '+file,()=>{
 const original=fs.readFileSync,paths=new Set([resolve(file),'/workspace/vy5-dependencies-20261101/'+file]);
 try{fs.readFileSync=function(path,...args){const v=original.call(this,path,...args);return paths.has(String(path))?(typeof v==='string'?v+'\n':Buffer.concat([v,Buffer.from('\n')])):v;};syncBuiltinESMExports();assert.throws(()=>verifyRethrowInputs('/workspace/vy5-dependencies-20261101'));}finally{fs.readFileSync=original;syncBuiltinESMExports();}
});
for(const file of ['lean.stdout','lean.stderr','lean.execution.json'])test('actual execution drift '+file,()=>{
 const original=fs.readFileSync;
 try{fs.readFileSync=function(path,...args){return String(path)===join(DIR,file)?'{}':original.call(this,path,...args);};syncBuiltinESMExports();assert.throws(()=>validateRethrowReport(r,DIR));}finally{fs.readFileSync=original;syncBuiltinESMExports();}
});
for(const target of ['/workspace/vy5-composition/scope-catch-20261101/readback-v1/report.json','/workspace/vy5-composition/attempt-20261101/native-v2/report.json'])test('sealed full reference cannot drift '+target,()=>{
 const original=fs.readFileSync;
 try{fs.readFileSync=function(path,...args){return String(path)===target?Buffer.from('{}'):original.call(this,path,...args);};syncBuiltinESMExports();assert.throws(()=>validateRethrowReport(r,DIR));}finally{fs.readFileSync=original;syncBuiltinESMExports();}
});
test('selected required rethrow catalog cannot disappear',()=>{
 const original=fs.readFileSync,target=resolve('tests/yul-composition/ledger.json'),root=JSON.parse(original(target));delete root.rethrowComponentEvidence;
 try{fs.readFileSync=function(path,...args){return String(path)===target?Buffer.from(JSON.stringify(root)):original.call(this,path,...args);};syncBuiltinESMExports();assert.throws(()=>validateRethrowReport(r,DIR));}finally{fs.readFileSync=original;syncBuiltinESMExports();}
});
