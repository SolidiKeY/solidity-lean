import test from 'node:test';
import assert from 'node:assert/strict';
import fs,{readFileSync} from 'node:fs';
import {syncBuiltinESMExports} from 'node:module';
import {join,resolve} from 'node:path';
import {validateAttemptModel,validateAttemptLedger,verifyAttemptInputs,validateAttemptReport} from './attempt-source.mjs';
const DIR='/workspace/vy5-composition/attempt-20261101/native-v2',report=JSON.parse(readFileSync(join(DIR,'report.json'))),clone=()=>structuredClone(report),word=n=>'0x'+BigInt(n).toString(16).padStart(64,'0');
test('actual attempt28componentlaws/sixSourcecases/24nativecalls leave full24/sixpending',()=>{
 validateAttemptReport(report,DIR);verifyAttemptInputs('/workspace/vy5-dependencies-20261101');const l=validateAttemptLedger();
 assert.equal(l.facts.length,28);assert.equal(l.fullCoverage,false);assert.equal(l.obligations.length,24);assert.equal(l.combinations.length,6);assert.equal(report.rows.length,4);assert.equal(report.rows.reduce((n,r)=>n+r.calls.length,0),24);assert.equal(report.fullProofGate,'pending');
});
for(const key of Object.keys(report.model))test('missing/malformed actual attempt model '+key,()=>{
 const x=structuredClone(report.model);delete x[key];assert.throws(()=>validateAttemptModel(x));const y=structuredClone(report.model);y[key]=null;assert.throws(()=>validateAttemptModel(y));
});
const models={
 'caller raw reset':m=>m.inputCells[3]='1',
 'caller bits cleaned':m=>m.cases[1].postRaw[0]='1',
 'attempt falsely rolledback poststate':m=>m.cases[1].postLogs.pop(),
 'attempt falsely kept only entry state':m=>m.cases[1].postLogs=[['1',[85]]],
 'source postlogs reversed':m=>m.sourceLogs.reverse(),
 'success misrouted to catch':m=>m.cases[0].routed={tag:'catch',bytes:[190,239],cells:m.cells,normal:true},
 'revert misrouted to success':m=>m.cases[1].routed={tag:'success',bytes:[222,173]},
 'captured halt discarded':m=>m.cases[1].captured={tag:'success',bytes:[]},
 'empty revert stale data':m=>m.cases[2].routed.bytes=[222,173],
 'panic swallowed':m=>m.cases[3].routed={tag:'success',bytes:[]},
 'panic code changed':m=>m.cases[3].captured.bytes[35]=17,
 'panic tail lost despite equal prefix':m=>m.cases[3].routed.bytes=m.cases[3].routed.bytes.slice(0,32),
 'timeout caught as empty':m=>m.cases[4].routed={tag:'catch',bytes:[],cells:null,normal:null},
 'stuck swallowed':m=>m.cases[5].routed={tag:'success',bytes:[]},
 'stuck reason lost':m=>m.cases[5].routed.reason='',
 'continuation timeout confused with source timeout':m=>m.zeroRevert={tag:'timeout'},
 'exhaustion data lost':m=>m.zeroRevert.bytes=[],
 'missing byte-length binding':m=>m.cells[3]='2305',
 'empty length treated nonempty':m=>m.emptyCells[3]='2307',
 'panic length wrong':m=>m.panicCells[3]='2307',
 'nonword alias overwritten':m=>m.nonword=8,
 'raw cleanup permitted':m=>m.rawClean=true,
 'case order changed':m=>m.cases.reverse(),
 'case omitted':m=>m.cases.pop()
};
for(const[name,change]of Object.entries(models))test(name,()=>{const x=structuredClone(report.model);change(x);assert.throws(()=>validateAttemptModel(x));});
const nativeMutants={
 'missing profile':r=>r.rows.pop(),
 'profile ordering':r=>r.rows.reverse(),
 'optimizer identity':r=>r.rows[0].optimized=true,
 'pipeline identity':r=>r.rows[0].pipeline='viaIR',
 'missing call':r=>r.rows[0].calls.pop(),
 'reordered calls':r=>r.rows[0].calls.reverse(),
 'wrong catch input identity':r=>r.rows[0].calls[2].capture.frames[1].input='0x',
 'wrong call ordinal':r=>r.rows[0].calls[2].capture.transaction=99,
 'wrong frame owner':r=>r.rows[0].calls[2].capture.frames[1].address='0x'+'34'.repeat(20),
 'wrong child caller':r=>r.rows[0].calls[2].capture.frames[2].caller='0x'+'34'.repeat(20),
 'missing nested success frame':r=>r.rows[0].calls[2].capture.frames.pop(),
 'retained child storage despite equal returns':r=>r.rows[0].calls[2].capture.post[r.rows[0].address].persistent[word(43)]=word(0xcd000003),
 'caller prefix storage rolledback':r=>r.rows[0].calls[2].capture.post[r.rows[0].address].persistent[word(48)]=word(0),
 'unused slot corrupted':r=>r.rows[0].calls[2].capture.post[r.rows[0].address].persistent[word(42)]=word(1),
 'missing persistent evidence':r=>delete r.rows[0].calls[2].capture.post[r.rows[0].address].persistent[word(43)],
 'wrong pre-state':r=>r.rows[0].calls[2].capture.pre[r.rows[0].address].persistent[word(48)]=word(0),
 'retained transient child':r=>r.rows[0].calls[2].capture.post[r.rows[0].address].transient[word(0)]=word(0x33),
 'missing transient state':r=>delete r.rows[0].calls[2].capture.post[r.rows[0].address].transient[word(0)],
 'wrong balance':r=>r.rows[0].calls[2].capture.post[r.rows[0].address].balance='1',
 'wrong caller nonce':r=>r.rows[0].calls[2].capture.post[r.rows[0].calls[2].capture.request.caller].nonce='99',
 'lost caller log prefix':r=>r.rows[0].calls[2].actual.logs=[],
 'child log wrongly retained':r=>r.rows[0].calls[2].actual.logs.push({emitter:r.rows[0].address,topics:[],data:'0x77'}),
 'empty returndata confused with dead':r=>r.rows[0].calls[3].capture.frames[1].output.bytes='0xdead',
 'nonempty returndata discarded':r=>r.rows[0].calls[2].capture.frames[1].output.bytes='0x',
 'stale catch buffer':r=>r.rows[0].calls[3].capture.frames[0].lastCallReturnData.bytes='0xfa',
 'missing frame memory':r=>r.rows[0].calls[2].capture.frames[1].regions=[],
 'wrong failure memory bytes':r=>{const w=r.rows[0].calls[2].capture.frames[1].regions.find(w=>w.opcode==='REVERT');const i=Number(w.offset)*2+2;w.bytes=w.bytes.slice(0,i)+'01'+w.bytes.slice(i+2);},
 'wrong empty failure length':r=>r.rows[0].calls[3].capture.frames[1].regions.find(w=>w.opcode==='REVERT').length='1',
 'missing nested rollback operation':r=>{const c=r.rows[0].calls[2].capture;c.operations=c.operations.filter(o=>!(o.kind==='revert'&&o.frame===1));},
 'wrong write owner':r=>r.rows[0].calls[2].capture.operations.find(o=>o.kind==='putStorage'&&o.slot===word(43)).address='0x'+'34'.repeat(20),
 'wrong write frame':r=>r.rows[0].calls[2].capture.operations.find(o=>o.kind==='putStorage'&&o.slot===word(43)).frame=0,
 'wrong write slot':r=>r.rows[0].calls[2].capture.operations.find(o=>o.kind==='putStorage'&&o.slot===word(43)).slot=word(42),
 'reordered physical writes':r=>{const c=r.rows[0].calls[2].capture;const i=c.operations.findIndex(o=>o.kind==='putStorage'&&o.slot===word(43));const j=c.operations.findLastIndex(o=>o.kind==='putStorage'&&o.slot===word(43));[c.operations[i],c.operations[j]]=[c.operations[j],c.operations[i]];},
 'false full proof':r=>r.fullProofGate='pass',
 'stale source hash':r=>r.inputHashes['tests/yul-composition/AttemptControls.sol']='0'.repeat(64),
 'stale consumer hash':r=>r.consumerHashes['Solidity/Yul/Composition/AttemptPhysical.lean']='0'.repeat(64),
 'stale runner':r=>r.runnerSha256='0'.repeat(64),
 'stale compiler receipt':r=>r.rows[0].receipt.inputSha256='0'.repeat(64)
};
for(const[name,mutate]of Object.entries(nativeMutants))test(name,()=>{const x=clone();mutate(x);assert.throws(()=>validateAttemptReport(x,DIR));});

for(const [name,change]of Object.entries({
 'pure success incorrectly nonstatic':r=>r.rows[0].calls[1].capture.frames[1].isStatic=false,
 'success wrong buffer':r=>r.rows[0].calls[1].capture.frames[0].lastCallReturnData.bytes='0x',
 'success wrong bytes':r=>r.rows[0].calls[1].capture.frames[1].output.bytes='0xdead',
 'panic wrong full catch bytes':r=>{const f=r.rows[0].calls[4].capture.frames[1];f.output.bytes=f.output.bytes.slice(0,-2)+'11';},
 'panic buffer missing tail':r=>r.rows[0].calls[4].capture.frames[0].lastCallReturnData.bytes=r.rows[0].calls[4].capture.frames[0].lastCallReturnData.bytes.slice(0,-8),
 'success writes callee state':r=>r.rows[0].calls[1].capture.post[r.rows[0].address].persistent[word(43)]=word(1)
}))test(name,()=>{const x=clone();change(x);assert.throws(()=>validateAttemptReport(x,DIR));});
for(const file of ['Solidity/Source/Machine.lean','Solidity/Source/Value.lean','Solidity/Source/Observe.lean','Solidity/Yul/Composition/CatchFunctionPhysical.lean','Solidity/Yul/Composition/AttemptPhysical.lean','tests/yul-composition/attempt-expectations.json','tests/yul-composition/attempt-component-ledger.json'])test('actual producer/consumer/oracle byte drift '+file,()=>{
 const original=fs.readFileSync,paths=new Set([resolve(file),'/workspace/vy5-dependencies-20261101/'+file]);
 try{fs.readFileSync=function(path,...args){const data=original.call(this,path,...args);if(paths.has(String(path)))return typeof data==='string'?data+'\n':Buffer.concat([data,Buffer.from('\n')]);return data;};syncBuiltinESMExports();assert.throws(()=>verifyAttemptInputs('/workspace/vy5-dependencies-20261101'));}finally{fs.readFileSync=original;syncBuiltinESMExports();}
});
for(const selector of ['attemptComponentEvidence','catchFunctionComponentEvidence'])test('required selected catalog '+selector,()=>{
 const original=fs.readFileSync,absolute=resolve('tests/yul-composition/ledger.json'),root=JSON.parse(original(absolute));delete root[selector];
 try{fs.readFileSync=function(path,...args){return String(path)===absolute?Buffer.from(JSON.stringify(root)):original.call(this,path,...args);};syncBuiltinESMExports();assert.throws(()=>validateAttemptReport(report,DIR));}finally{fs.readFileSync=original;syncBuiltinESMExports();}
});
for(const file of ['lean.stdout','lean.stderr','lean.execution.json'])test('retained actual execution '+file+' cannot drift',()=>{
 const original=fs.readFileSync,absolute=join(DIR,file);
 try{fs.readFileSync=function(path,...args){if(String(path)===absolute)return args[0]==='utf8'?'{}':Buffer.from('{}');return original.call(this,path,...args);};syncBuiltinESMExports();assert.throws(()=>validateAttemptReport(report,DIR));}finally{fs.readFileSync=original;syncBuiltinESMExports();}
});
