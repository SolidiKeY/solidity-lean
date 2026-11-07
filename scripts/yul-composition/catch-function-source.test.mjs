import test from 'node:test';
import assert from 'node:assert/strict';
import fs,{readFileSync,writeFileSync,mkdtempSync,copyFileSync,rmSync} from 'node:fs';
import {syncBuiltinESMExports} from 'node:module';
import {join,resolve} from 'node:path';
import {validateCatchFunctionModel,validateCatchFunctionInput,validateCatchFunctionLedger,verifyCatchFunctionInputs,validateCatchFunctionReport} from './catch-function-source.mjs';
const DIR=process.env.VY5_CATCH_FUNCTION_REPORT_DIR??'/workspace/vy5-composition/catch-function-20261101/native-v1';
const report=JSON.parse(readFileSync(join(DIR,'report.json'))),clone=()=>structuredClone(report),word=n=>'0x'+BigInt(n).toString(16).padStart(64,'0');
test('actual raw-catch component retains24laws/all24obligations/sixcombinations pending and40ordered nativecalls',()=>{
 validateCatchFunctionReport(report,DIR);verifyCatchFunctionInputs('/workspace/vy5-dependencies-20261101');const l=validateCatchFunctionLedger();
 assert.equal(l.facts.length,24);assert.equal(l.obligations.length,24);assert.equal(l.combinations.length,6);assert.equal(l.fullCoverage,false);
 assert.equal(report.rows.length,4);assert.equal(report.rows.reduce((n,r)=>n+r.calls.length,0),40);assert.equal(report.fullProofGate,'pending');
});
for(const key of Object.keys(report.model))test('missing/malformed actual raw-catch model '+key,()=>{
 const x=structuredClone(report.model);delete x[key];assert.throws(()=>validateCatchFunctionModel(x));
 const y=structuredClone(report.model);y[key]=null;assert.throws(()=>validateCatchFunctionModel(y));
});
const modelMutants={
 'wrong callee confused with nested':m=>m.wrongCells[3]=m.cells[3],
 'missing leave poison ignored':m=>m.poisonCells[3]=m.cells[3],
 'raw input reset unnoticed':m=>m.resetCells[3]=m.cells[3],
 'wrong indexed input arity':m=>m.arities[0]=[2,1],
 'wrong indexed result arity':m=>m.arities[1]=[1,2],
 'caller raw bool cleaned':m=>m.inputCells[0]='1',
 'dirty uint8 truncated on continuation':m=>m.cells[3]='1',
 'caller raw words reset across rollback':m=>m.inputCells[3]='1',
 'wrong catch addend':m=>m.cells[3]='1794',
 'aliased same-type locals':m=>m.cells[4]=m.cells[1],
 'lost function highbits':m=>m.cells[5]='4294967295',
 'lost nonword memoryalias':m=>m.nonwordId=8,
 'overwritten caller heap':m=>m.heapBytes=[170,0],
 'lost caller Source logs':m=>m.sourceLogs=[],
 'lost World log prefix':m=>m.worldLogs=[],
 'wrong log emitter':m=>m.worldLogs[0].emitter='2',
 'failed bytes dropped':m=>m.caughtBytes=[],
 'failed bytes reordered':m=>m.caughtBytes.reverse(),
 'empty failure treated stale':m=>m.emptyCaughtBytes=[250],
 'nonempty copy wrongdirection':m=>m.targetBytes=[238,173,222,238],
 'empty copy unexpectedly writes':m=>m.emptyTargetBytes=[238,0,238],
 'lost physical outer rollback':m=>m.physical.outer=m.physical.child,
 'lost raw physical padding':m=>m.physical.child='3',
 'clean bridge allowed':m=>m.cleanBridgeAccepted=true,
 'raw Source resume allowed':m=>m.rawResumeRefused=false,
 'mislabelled catch control':m=>m.flow=false,
 'reordered horizons':m=>m.horizons.reverse(),
 'dropped horizon':m=>m.horizons.pop(),
 'timeout treated completed':m=>m.horizons[0].outcome=m.horizons[6].outcome
};
for(const[name,mutate]of Object.entries(modelMutants))test(name,()=>{const x=structuredClone(report.model);mutate(x);assert.throws(()=>validateCatchFunctionModel(x));});
for(const key of Object.keys(report.model.journalLengths))test('wrong coupled journal '+key,()=>{const x=structuredClone(report.model);x.journalLengths[key]++;assert.throws(()=>validateCatchFunctionModel(x));});
const nativeMutants={
 'missing profile':r=>r.rows.pop(),
 'profile ordering':r=>r.rows.reverse(),
 'optimizer identity':r=>r.rows[0].optimized=true,
 'pipeline identity':r=>r.rows[0].pipeline='viaIR',
 'missing call':r=>r.rows[0].calls.pop(),
 'reordered calls':r=>r.rows[0].calls.reverse(),
 'wrong catch input identity':r=>r.rows[0].calls[1].capture.frames[1].input='0x',
 'wrong call ordinal':r=>r.rows[0].calls[1].capture.transaction=99,
 'wrong frame owner':r=>r.rows[0].calls[1].capture.frames[1].address='0x'+'34'.repeat(20),
 'wrong child caller':r=>r.rows[0].calls[1].capture.frames[2].caller='0x'+'34'.repeat(20),
 'missing nested success frame':r=>r.rows[0].calls[1].capture.frames.pop(),
 'retained child storage despite equal returns':r=>r.rows[0].calls[1].capture.post[r.rows[0].address].persistent[word(43)]=word(0xcd000003),
 'caller prefix storage rolledback':r=>r.rows[0].calls[1].capture.post[r.rows[0].address].persistent[word(48)]=word(0),
 'unused slot corrupted':r=>r.rows[0].calls[1].capture.post[r.rows[0].address].persistent[word(42)]=word(1),
 'missing persistent evidence':r=>delete r.rows[0].calls[1].capture.post[r.rows[0].address].persistent[word(43)],
 'wrong pre-state':r=>r.rows[0].calls[1].capture.pre[r.rows[0].address].persistent[word(48)]=word(7),
 'retained transient child':r=>r.rows[0].calls[1].capture.post[r.rows[0].address].transient[word(0)]=word(0x33),
 'missing transient state':r=>delete r.rows[0].calls[1].capture.post[r.rows[0].address].transient[word(0)],
 'wrong balance':r=>r.rows[0].calls[1].capture.post[r.rows[0].address].balance='1',
 'wrong caller nonce':r=>r.rows[0].calls[1].capture.post[r.rows[0].calls[1].capture.request.caller].nonce='99',
 'lost caller log prefix':r=>r.rows[0].calls[1].actual.logs=[],
 'child log wrongly retained':r=>r.rows[0].calls[1].actual.logs.push({emitter:r.rows[0].address,topics:[],data:'0x77'}),
 'empty returndata confused with dead':r=>r.rows[0].calls[5].capture.frames[1].output.bytes='0xdead',
 'nonempty returndata discarded':r=>r.rows[0].calls[1].capture.frames[1].output.bytes='0x',
 'stale catch buffer':r=>r.rows[0].calls[5].capture.frames[0].lastCallReturnData.bytes='0xfa',
 'missing frame memory':r=>r.rows[0].calls[1].capture.frames[1].regions=[],
 'wrong failure memory bytes':r=>{const w=r.rows[0].calls[1].capture.frames[1].regions.find(w=>w.opcode==='REVERT');const i=Number(w.offset)*2+2;w.bytes=w.bytes.slice(0,i)+'01'+w.bytes.slice(i+2);},
 'wrong empty failure length':r=>r.rows[0].calls[5].capture.frames[1].regions.find(w=>w.opcode==='REVERT').length='1',
 'missing nested rollback operation':r=>{const c=r.rows[0].calls[1].capture;c.operations=c.operations.filter(o=>!(o.kind==='revert'&&o.frame===1));},
 'wrong write owner':r=>r.rows[0].calls[1].capture.operations.find(o=>o.kind==='putStorage'&&o.slot===word(43)).address='0x'+'34'.repeat(20),
 'wrong write frame':r=>r.rows[0].calls[1].capture.operations.find(o=>o.kind==='putStorage'&&o.slot===word(43)).frame=0,
 'wrong write slot':r=>r.rows[0].calls[1].capture.operations.find(o=>o.kind==='putStorage'&&o.slot===word(43)).slot=word(42),
 'reordered physical writes':r=>{const c=r.rows[0].calls[1].capture;const i=c.operations.findIndex(o=>o.kind==='putStorage'&&o.slot===word(43));const j=c.operations.findLastIndex(o=>o.kind==='putStorage'&&o.slot===word(43));[c.operations[i],c.operations[j]]=[c.operations[j],c.operations[i]];},
 'false full proof':r=>r.fullProofGate='pass',
 'stale source hash':r=>r.inputHashes['tests/yul-composition/CatchFunctionPhysicalControls.sol']='0'.repeat(64),
 'stale consumer hash':r=>r.consumerHashes['Solidity/Yul/Composition/CatchFunctionPhysical.lean']='0'.repeat(64),
 'stale runner':r=>r.runnerSha256='0'.repeat(64),
 'stale compiler receipt':r=>r.rows[0].receipt.inputSha256='0'.repeat(64)
};
for(const[name,mutate]of Object.entries(nativeMutants))test(name,()=>{const x=clone();mutate(x);assert.throws(()=>validateCatchFunctionReport(x,DIR));});
for(const file of ['Solidity/Yul/Composition/RawCatchPhysical.lean','Solidity/Yul/Composition/RecursivePhysical.lean','Solidity/Yul/Composition/CatchFunctionPhysical.lean','tests/yul-composition/catch-function-expectations.json','tests/yul-composition/catch-function-component-ledger.json'])test('actual dependency/source bytes drift '+file,()=>{
 const original=fs.readFileSync,paths=new Set([resolve(file),'/workspace/vy5-dependencies-20261101/'+file]);
 try{fs.readFileSync=function(path,...args){const data=original.call(this,path,...args);if(paths.has(String(path)))return typeof data==='string'?data+'\n':Buffer.concat([data,Buffer.from('\n')]);return data;};syncBuiltinESMExports();assert.throws(()=>verifyCatchFunctionInputs('/workspace/vy5-dependencies-20261101'));}
 finally{fs.readFileSync=original;syncBuiltinESMExports();}
});
for(const selector of ['catchFunctionComponentEvidence','rawCatchComponentEvidence','recursiveComponentEvidence'])test('required selected catalog '+selector+' cannot disappear',()=>{
 const original=fs.readFileSync,absolute=resolve('tests/yul-composition/ledger.json'),root=JSON.parse(original(absolute));delete root[selector];
 try{fs.readFileSync=function(path,...args){return String(path)===absolute?Buffer.from(JSON.stringify(root)):original.call(this,path,...args);};syncBuiltinESMExports();assert.throws(()=>validateCatchFunctionReport(report,DIR));}finally{fs.readFileSync=original;syncBuiltinESMExports();}
});
test('retained actual Lean receipt cannot disappear or change',()=>{
 const temp=mkdtempSync('/workspace/vy5-composition/catch-function-20261101/test-');
 try{for(const name of ['lean.stdout','lean.stderr','lean.execution.json'])copyFileSync(join(DIR,name),join(temp,name));
 for(const [name,value]of [['lean.stdout','{}'],['lean.stderr','error'],['lean.execution.json','{}']]){writeFileSync(join(temp,name),value);assert.throws(()=>validateCatchFunctionReport(report,temp));copyFileSync(join(DIR,name),join(temp,name));}
 rmSync(join(temp,'lean.stdout'));assert.throws(()=>validateCatchFunctionReport(report,temp));
 }finally{rmSync(temp,{recursive:true});}
});
