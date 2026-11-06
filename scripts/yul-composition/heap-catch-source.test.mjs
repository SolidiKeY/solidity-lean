import test from 'node:test';
import assert from 'node:assert/strict';
import fs,{readFileSync} from 'node:fs';
import {syncBuiltinESMExports} from 'node:module';
import {join,resolve} from 'node:path';
import {verifyHeapInputs,validateHeapModel,validateHeapReport} from './heap-catch-source.mjs';
const DIR='/workspace/vy5-composition/heap-catch-20261101/readback-v1',r=JSON.parse(readFileSync(join(DIR,'report.json')));
test('actual typed heap38laws/sixSourcecases/16bytecomparisons across4historicalprofiles preserve fullpending',()=>{
 validateHeapReport(r,DIR);const l=JSON.parse(readFileSync('tests/yul-composition/heap-catch-component-ledger.json'));assert.equal(l.facts.length,38);assert.equal(l.obligations.length,24);assert.equal(l.combinations.length,6);assert.equal(l.fullCoverage,false);assert.equal(r.rows.length,4);assert.equal(r.rows.reduce((n,r)=>n+r.comparisons.length,0),16);assert.equal(r.nativeExecution,'historical-replay-only');
});
for(const key of Object.keys(r.model))test('missing/malformed heap model '+key,()=>{const m=structuredClone(r.model);delete m[key];assert.throws(()=>validateHeapModel(m));const n=structuredClone(r.model);n[key]=null;assert.throws(()=>validateHeapModel(n));});
const mutations={
 'logical index falsely treated as physical':m=>m.addressDomain='evm-address',
 'wrong allocated logical index':m=>m.cases[1].result.ref.logicalIndex=0,
 'lost full caught bytes':m=>m.cases[1].result.bytes=[],
 'wrong allocated bytes despite equal length':m=>m.cases[1].object.bytes=[173,222],
 'wrong length':m=>m.cases[1].object.length=1,
 'empty allocation treated absent':m=>m.cases[2].object=null,
 'empty allocation skipped':m=>m.cases[2].next=1,
 'panic tail lost':m=>m.cases[3].object.bytes=m.cases[3].object.bytes.slice(0,32),
 'panic code wrong':m=>m.cases[3].result.bytes[35]=17,
 'success allocates catch':m=>m.cases[0].next=2,
 'timeout swallowed':m=>m.cases[4].result={tag:'success',bytes:[]},
 'stuck allocated':m=>m.cases[5].object={kind:'bytes',bytes:[],length:0},
 'raw caller reset':m=>m.cases[1].raw[3]='1',
 'dirty bool cleaned':m=>m.cases[1].raw[0]='1',
 'callee state rolledback incorrectly':m=>m.cases[1].logs=[['1',[85]]],
 'old alias overwritten':m=>m.cases[1].alias.bytes=[222,173],
 'nonword alias changed after read':m=>m.continuations[0].alias=null,
 'readback wrong data':m=>m.continuations[0].allocated.bytes=[0,0],
 'continuation ran on reset state':m=>m.continuations[0].cells[3]='515',
 'continuation cleans raw':m=>m.continuations[0].clean=true,
 'bad ref rejection falsely atomic':m=>m.badAllocation.next=1,
 'bad ref object discarded':m=>m.badAllocation.object=null,
 'bad ref halt swallowed':m=>m.badAllocation.outcome={tag:'success'},
 'nonbyte read became empty bytes':m=>m.nonbyteRead={tag:'success',bytes:[]},
 'dangling read became empty bytes':m=>m.danglingRead={tag:'success',bytes:[]},
 'case ordering':m=>m.cases.reverse()
};
for(const[name,change]of Object.entries(mutations))test(name,()=>{const m=structuredClone(r.model);change(m);assert.throws(()=>validateHeapModel(m));});
for(const[name,change]of Object.entries({
 'false new EVM execution':r=>r.nativeExecution='fresh',
 'false fullproof':r=>r.fullProofGate='pass',
 'missing reference profile':r=>r.rows.pop(),
 'reordered profiles':r=>r.rows.reverse(),
 'stale reference SHA':r=>r.referenceSha256='0'.repeat(64),
 'source/readback link wrongbytes':r=>r.rows[0].comparisons[1].bytes=[0,0],
 'missing fullpanic link':r=>r.rows[0].comparisons.pop(),
 'fake physical index':r=>r.rows[0].comparisons[1].logicalReference.logicalIndex=224,
 'stale source body':r=>r.inputHashes['Solidity/Yul/Composition/HeapCatchPhysical.lean']='0'.repeat(64),
 'stale runner':r=>r.runnerSha256='0'.repeat(64)
}))test(name,()=>{const x=structuredClone(r);change(x);assert.throws(()=>validateHeapReport(x,DIR));});
for(const file of ['Solidity/Source/State.lean','Solidity/Source/Machine.lean','Solidity/Source/Eval.lean','Solidity/Source/Hoare.lean','Solidity/Yul/Composition/HeapCatchPhysical.lean','Solidity/Yul/Composition/AttemptPhysical.lean','tests/yul-composition/heap-catch-expectations.json','tests/yul-composition/heap-catch-component-ledger.json'])test('actual private/main source bytes drift '+file,()=>{
 const original=fs.readFileSync,paths=new Set([resolve(file),'/workspace/vy5-dependencies-20261101/'+file]);
 try{fs.readFileSync=function(path,...args){const v=original.call(this,path,...args);return paths.has(String(path))?(typeof v==='string'?v+'\n':Buffer.concat([v,Buffer.from('\n')])):v;};syncBuiltinESMExports();assert.throws(()=>verifyHeapInputs('/workspace/vy5-dependencies-20261101'));}finally{fs.readFileSync=original;syncBuiltinESMExports();}
});
for(const file of ['lean.stdout','lean.stderr','lean.execution.json'])test('retained new Source execution cannot drift '+file,()=>{
 const original=fs.readFileSync;
 try{fs.readFileSync=function(path,...args){return String(path)===join(DIR,file)?'{}':original.call(this,path,...args);};syncBuiltinESMExports();assert.throws(()=>validateHeapReport(r,DIR));}finally{fs.readFileSync=original;syncBuiltinESMExports();}
});
test('prior reference file cannot drift despite declared SHA',()=>{
 const original=fs.readFileSync,target='/workspace/vy5-composition/attempt-20261101/native-v2/report.json';
 try{fs.readFileSync=function(path,...args){return String(path)===target?Buffer.from('{}'):original.call(this,path,...args);};syncBuiltinESMExports();assert.throws(()=>validateHeapReport(r,DIR));}finally{fs.readFileSync=original;syncBuiltinESMExports();}
});
test('selected heap obligation cannot disappear',()=>{
 const original=fs.readFileSync,target=resolve('tests/yul-composition/ledger.json'),root=JSON.parse(original(target));delete root.heapCatchComponentEvidence;
 try{fs.readFileSync=function(path,...args){return String(path)===target?Buffer.from(JSON.stringify(root)):original.call(this,path,...args);};syncBuiltinESMExports();assert.throws(()=>validateHeapReport(r,DIR));}finally{fs.readFileSync=original;syncBuiltinESMExports();}
});
