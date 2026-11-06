import test from 'node:test';
import assert from 'node:assert/strict';
import fs,{readFileSync} from 'node:fs';
import {syncBuiltinESMExports} from 'node:module';
import {join,resolve} from 'node:path';
import {verifyModifierInputs,validateModifierModel,validateModifierReport} from './modifier-source.mjs';
const DIR='/workspace/vy5-composition/modifier-body-20261102/readback-v1',r=JSON.parse(readFileSync(join(DIR,'report.json')));
test('actual30laws/twoSourcepipelines42cases/two directplaceholders, no globalclosure',()=>{
 validateModifierReport(r,DIR);const l=JSON.parse(readFileSync('tests/yul-composition/modifier-ledger.json'));assert.equal(l.facts.length,30);assert.equal(l.obligations.length,24);assert.equal(l.combinations.length,6);assert.equal(l.fullCoverage,false);assert.deepEqual(r.model.pipelines.map(p=>p.pipeline),['legacy','viaIR']);assert.equal(r.model.pipelines.reduce((n,p)=>n+p.cases.length,0),42);assert.equal(r.rows.length,0);assert.equal(r.nativeComparisons.length,0);assert.equal(r.fullProofGate,'pending');
});
for(const key of Object.keys(r.model))test('missing/malformed model '+key,()=>{const m=structuredClone(r.model);delete m[key];assert.throws(()=>validateModifierModel(m));const n=structuredClone(r.model);n[key]=null;assert.throws(()=>validateModifierModel(n));});
const mutations={
 'logical index falsely physical':m=>m.addressDomain='evm-address',
 'false frontend admission':m=>m.scope='frontend-admitted',
 'missing actual source pipeline':m=>m.pipelines.pop(),
 'pipeline order':m=>m.pipelines.reverse(),
 'missing source call':m=>m.pipelines[0].cases.pop(),
 'case order':m=>m.pipelines[0].cases.reverse(),
 'lost full DEAD bytes':m=>m.pipelines[0].cases[2].result.bytes=[],
 'same-length AABB normalized to DEAD':m=>m.pipelines[0].cases[5].result.bytes=[222,173],
 'panic full tail changed':m=>m.pipelines[1].cases[4].result.bytes[35]=17,
 'empty revert became success':m=>m.pipelines[0].cases[3].result.tag='success',
 'saved bool frame replaced by parameter frame':m=>m.pipelines[0].cases[2].after.frame=m.pipelines[0].directPlaceholder.after.frame,
 'saved bool value lost':m=>m.pipelines[0].cases[2].after.frame.bool=false,
 'saved frame always default empty':m=>m.pipelines[0].cases[2].after.frame={types:[],bool:null,refs:[null,null]},
 'alternate frame incorrectly forced bool':m=>m.pipelines[0].cases[20].after.frame=m.pipelines[0].cases[2].after.frame,
 'alternate frame ref wrong':m=>m.pipelines[1].cases[20].after.frame.refs[0].logicalIndex=1,
 'low fuel hidden as revert':m=>m.pipelines[0].cases[6].result={tag:'revert',bytes:[222,173]},
 'late timeout loses finally restoration':m=>m.pipelines[1].cases[13].after.frame=m.pipelines[1].directPlaceholder.after.frame,
 'wrong low fuel message':m=>m.pipelines[0].cases[9].result={tag:'stuck',reason:'frame'},
 'missing modifier falsely passes':m=>m.pipelines[0].cases[14].result={tag:'revert',bytes:[222,173]},
 'modifier parameter mismatch swallowed':m=>m.pipelines[0].cases[15].result.reason='other',
 'missing function swallowed':m=>m.pipelines[0].cases[16].result.tag='success',
 'invalid call frame accepted':m=>m.pipelines[0].cases[17].result={tag:'revert',bytes:[222,173]},
 'placeholder outside modifier accepted':m=>m.pipelines[0].cases[18].result.tag='success',
 'placeholder invalid frame accepted':m=>m.pipelines[0].cases[19].result={tag:'revert',bytes:[222,173]},
 'direct placeholder falsely restores bool frame':m=>m.pipelines[0].directPlaceholder.after.frame=m.pipelines[0].cases[2].after.frame,
 'direct placeholder wrong parameter order':m=>m.pipelines[0].directPlaceholder.before.frame.refs.reverse(),
 'direct placeholder loses bytes':m=>m.pipelines[1].directPlaceholder.result.bytes.pop(),
 'raw uint8 reset':m=>m.pipelines[0].cases[2].after.raw[3]='1',
 'raw bool cleaned':m=>m.pipelines[0].cases[2].after.raw[0]='1',
 'nonword alias overwritten':m=>m.pipelines[0].cases[2].after.alias.bytes=[222,173],
 'heap catch bytes corrupted with equal return':m=>m.pipelines[0].cases[2].after.object.bytes=[173,222],
 'heap index allocated again':m=>m.pipelines[0].cases[2].after.next=3,
 'caller prefix log lost':m=>m.pipelines[0].cases[2].after.logs=[],
 'clean resumption enabled':m=>m.pipelines[0].cases[2].after.clean=true,
 'before saved frame mislabelled':m=>m.pipelines[1].cases[2].before.frame.bool=false
};
for(const[name,change]of Object.entries(mutations))test(name,()=>{const m=structuredClone(r.model);change(m);assert.throws(()=>validateModifierModel(m));});
for(const[name,change]of Object.entries({
 'false freshEVM':r=>r.nativeExecution='fresh',
 'false fullproof':r=>r.fullProofGate='pass',
 'invented native rethrow comparison':r=>r.nativeComparisons=[{status:'match'}],
 'old caughtcall relabelled new path':r=>r.rows=[{status:'match'}],
 'lost historical full24validation':r=>r.historicalValidation.orderedCalls=16,
 'false historical role':r=>r.historicalValidation.role='rethrow-source adequacy',
 'stale parent hash':r=>r.referenceSha256='0'.repeat(64),
 'stale own source':r=>r.inputHashes['Solidity/Yul/Composition/ModifierPhysical.lean']='0'.repeat(64),
 'stale runner':r=>r.runnerSha256='0'.repeat(64)
}))test(name,()=>{const x=structuredClone(r);change(x);assert.throws(()=>validateModifierReport(x,DIR));});
for(const file of ['Solidity/Source/Decls.lean','Solidity/Source/Syntax.lean','Solidity/Source/Types.lean','Solidity/Source/Value.lean','Solidity/Source/Elaborated.lean','Solidity/Source/State.lean','Solidity/Source/Machine.lean','Solidity/Source/Eval.lean','Solidity/Source/Resolved.lean','Solidity/Source/Hoare.lean','Solidity/Yul/Composition/ModifierPhysical.lean','Solidity/Yul/Composition/ScopeCatchPhysical.lean','tests/yul-composition/ModifierDriver.lean','tests/yul-composition/modifier-expectations.json','tests/yul-composition/modifier-ledger.json'])test('actual private/main body drift '+file,()=>{
 const original=fs.readFileSync,paths=new Set([resolve(file),'/workspace/vy5-dependencies-20261101/'+file]);
 try{fs.readFileSync=function(path,...args){const v=original.call(this,path,...args);return paths.has(String(path))?(typeof v==='string'?v+'\n':Buffer.concat([v,Buffer.from('\n')])):v;};syncBuiltinESMExports();assert.throws(()=>verifyModifierInputs('/workspace/vy5-dependencies-20261101'));}finally{fs.readFileSync=original;syncBuiltinESMExports();}
});
for(const file of ['lean.stdout','lean.stderr','lean.execution.json'])test('actual execution drift '+file,()=>{
 const original=fs.readFileSync;
 try{fs.readFileSync=function(path,...args){return String(path)===join(DIR,file)?'{}':original.call(this,path,...args);};syncBuiltinESMExports();assert.throws(()=>validateModifierReport(r,DIR));}finally{fs.readFileSync=original;syncBuiltinESMExports();}
});
for(const target of ['/workspace/vy5-composition/runtime-block-20261102/readback-v1/report.json','/workspace/vy5-composition/attempt-20261101/native-v2/report.json'])test('sealed full reference cannot drift '+target,()=>{
 const original=fs.readFileSync;
 try{fs.readFileSync=function(path,...args){return String(path)===target?Buffer.from('{}'):original.call(this,path,...args);};syncBuiltinESMExports();assert.throws(()=>validateModifierReport(r,DIR));}finally{fs.readFileSync=original;syncBuiltinESMExports();}
});
test('selected required rethrow catalog cannot disappear',()=>{
 const original=fs.readFileSync,target=resolve('tests/yul-composition/ledger.json'),root=JSON.parse(original(target));delete root.modifierEvidence;
 try{fs.readFileSync=function(path,...args){return String(path)===target?Buffer.from(JSON.stringify(root)):original.call(this,path,...args);};syncBuiltinESMExports();assert.throws(()=>validateModifierReport(r,DIR));}finally{fs.readFileSync=original;syncBuiltinESMExports();}
});

 test('original strict five native journal failures remain immutableFAIL',()=>{const path='/workspace/vy5-composition/native-rethrow-20261101/original-v3/report.json',original=fs.readFileSync;try{fs.readFileSync=function(file,...args){if(String(file)===path){const o=JSON.parse(original(file));o.validation='pass';return Buffer.from(JSON.stringify(o));}return original.call(this,file,...args);};syncBuiltinESMExports();assert.throws(()=>validateModifierReport(r,DIR));}finally{fs.readFileSync=original;syncBuiltinESMExports();}});
