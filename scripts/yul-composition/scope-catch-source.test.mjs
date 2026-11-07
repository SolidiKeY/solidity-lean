import test from 'node:test';
import assert from 'node:assert/strict';
import fs,{readFileSync} from 'node:fs';
import {syncBuiltinESMExports} from 'node:module';
import {join,resolve} from 'node:path';
import {verifyScopeInputs,validateScopeModel,validateScopeReport} from './scope-catch-source.mjs';
const DIR='/workspace/vy5-composition/scope-catch-20261101/readback-v1',r=JSON.parse(readFileSync(join(DIR,'report.json')));
test('actual typed scope28laws/sixSourcecases/16bytecomparisons across4historicalprofiles preserve fullpending',()=>{
 validateScopeReport(r,DIR);const l=JSON.parse(readFileSync('tests/yul-composition/scope-catch-component-ledger.json'));assert.equal(l.facts.length,28);assert.equal(l.obligations.length,24);assert.equal(l.combinations.length,6);assert.equal(l.fullCoverage,false);assert.equal(r.rows.length,4);assert.equal(r.rows.reduce((n,r)=>n+r.comparisons.length,0),16);assert.equal(r.nativeExecution,'historical-replay-only');
});
for(const key of Object.keys(r.model))test('missing/malformed heap model '+key,()=>{const m=structuredClone(r.model);delete m[key];assert.throws(()=>validateScopeModel(m));const n=structuredClone(r.model);n[key]=null;assert.throws(()=>validateScopeModel(n));});
const mutations={
 'logical index falsely physical':m=>m.addressDomain='evm-address',
 'missing scope type':m=>m.innerTypes.pop(),
 'wrong scope type':m=>m.outerTypes[0]='bool',
 'wrong bound ref':m=>m.cases[1].result.ref.logicalIndex=0,
 'wrong inner reference order':m=>m.cases[1].result.inner.reverse(),
 'wrong captured bytes same length':m=>m.cases[1].result.bytes=[173,222],
 'wrong full byte tail':m=>m.cases[3].result.bytes.pop(),
 'wrong local restore':m=>m.cases[1].restored.logicalIndex=1,
 'empty scope lost':m=>m.cases[2].result.inner=[],
 'panic changed':m=>m.cases[3].object.bytes[35]=17,
 'success enters scope':m=>m.cases[0].next=2,
 'timeout swallowed':m=>m.cases[4].result={tag:'success',bytes:[]},
 'stuck caught':m=>m.cases[5].result.tag='scoped',
 'raw caller reset':m=>m.cases[1].raw[3]='1',
 'dirty bool cleaned':m=>m.cases[1].raw[0]='1',
 'old alias overwritten':m=>m.cases[1].alias.bytes=[222,173],
 'retained Source logs rolledback':m=>m.cases[1].logs.pop(),
 'continuation numeric right but bytes wrong':m=>m.continuations[0].read=[170,187],
 'continuation wrong reference':m=>m.continuations[0].ref.logicalIndex=0,
 'continuation caller reset':m=>m.continuations[0].cells[3]='515',
 'raw continuation cleaned':m=>m.continuations[0].clean=true,
 'continuation old alias lost':m=>m.continuations[0].alias=null,
 'halt mutated scope leaks':m=>m.haltScopes[0].restored.logicalIndex=2,
 'halt wrong bytes':m=>m.haltScopes[0].outcome.bytes=[173,222],
 'halt swallowed':m=>m.haltScopes[3].outcome={tag:'success'},
 'halt poststate rollback falsely implied':m=>m.haltScopes[0].logs.shift(),
 'halt raw caller reset':m=>m.haltScopes[4].raw[3]='1',
 'wrong index falsely reads caught bytes':m=>m.wrongIndex.bytes=[222,173],
 'wrong scope type accepted':m=>m.wrongType.outcome={tag:'success'},
 'wrong type loses restoration':m=>m.wrongType.restored.logicalIndex=1,
 'case order':m=>m.cases.reverse(),
 'halt ordering':m=>m.haltScopes.reverse()
};
for(const[name,change]of Object.entries(mutations))test(name,()=>{const m=structuredClone(r.model);change(m);assert.throws(()=>validateScopeModel(m));});
for(const[name,change]of Object.entries({
 'false new EVM execution':r=>r.nativeExecution='fresh',
 'false fullproof':r=>r.fullProofGate='pass',
 'missing reference profile':r=>r.rows.pop(),
 'reordered profiles':r=>r.rows.reverse(),
 'stale reference SHA':r=>r.referenceSha256='0'.repeat(64),
 'source/readback link wrongbytes':r=>r.rows[0].comparisons[1].bytes=[0,0],
 'missing fullpanic link':r=>r.rows[0].comparisons.pop(),
 'fake physical index':r=>r.rows[0].comparisons[1].logicalReference.logicalIndex=224,
 'stale source body':r=>r.inputHashes['Solidity/Yul/Composition/ScopeCatchPhysical.lean']='0'.repeat(64),
 'stale runner':r=>r.runnerSha256='0'.repeat(64)
}))test(name,()=>{const x=structuredClone(r);change(x);assert.throws(()=>validateScopeReport(x,DIR));});
for(const file of ['Solidity/Source/State.lean','Solidity/Source/Machine.lean','Solidity/Source/Eval.lean','Solidity/Source/Hoare.lean','Solidity/Source/Resolved.lean','Solidity/Yul/Composition/ScopeCatchPhysical.lean','Solidity/Yul/Composition/AttemptPhysical.lean','tests/yul-composition/scope-catch-expectations.json','tests/yul-composition/scope-catch-component-ledger.json'])test('actual private/main source bytes drift '+file,()=>{
 const original=fs.readFileSync,paths=new Set([resolve(file),'/workspace/vy5-dependencies-20261101/'+file]);
 try{fs.readFileSync=function(path,...args){const v=original.call(this,path,...args);return paths.has(String(path))?(typeof v==='string'?v+'\n':Buffer.concat([v,Buffer.from('\n')])):v;};syncBuiltinESMExports();assert.throws(()=>verifyScopeInputs('/workspace/vy5-dependencies-20261101'));}finally{fs.readFileSync=original;syncBuiltinESMExports();}
});
for(const file of ['lean.stdout','lean.stderr','lean.execution.json'])test('retained new Source execution cannot drift '+file,()=>{
 const original=fs.readFileSync;
 try{fs.readFileSync=function(path,...args){return String(path)===join(DIR,file)?'{}':original.call(this,path,...args);};syncBuiltinESMExports();assert.throws(()=>validateScopeReport(r,DIR));}finally{fs.readFileSync=original;syncBuiltinESMExports();}
});
test('prior reference file cannot drift despite declared SHA',()=>{
 const original=fs.readFileSync,target='/workspace/vy5-composition/heap-catch-20261101/readback-v1/report.json';
 try{fs.readFileSync=function(path,...args){return String(path)===target?Buffer.from('{}'):original.call(this,path,...args);};syncBuiltinESMExports();assert.throws(()=>validateScopeReport(r,DIR));}finally{fs.readFileSync=original;syncBuiltinESMExports();}
});
test('selected heap obligation cannot disappear',()=>{
 const original=fs.readFileSync,target=resolve('tests/yul-composition/ledger.json'),root=JSON.parse(original(target));delete root.scopeCatchComponentEvidence;
 try{fs.readFileSync=function(path,...args){return String(path)===target?Buffer.from(JSON.stringify(root)):original.call(this,path,...args);};syncBuiltinESMExports();assert.throws(()=>validateScopeReport(r,DIR));}finally{fs.readFileSync=original;syncBuiltinESMExports();}
});
