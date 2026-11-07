import test from 'node:test';
import assert from 'node:assert/strict';
import fs,{readFileSync,writeFileSync,mkdtempSync,copyFileSync,rmSync} from 'node:fs';
import {syncBuiltinESMExports} from 'node:module';
import {tmpdir} from 'node:os';
import {join,resolve} from 'node:path';
import {validateRecursiveModel,validateRecursiveInput,validateRecursiveLedger,verifyRecursiveInputs,validateRecursiveReport} from './recursive-source.mjs';
const DIR=process.env.VY5_RECURSIVE_REPORT_DIR??'/workspace/vy5-composition/recursive-source-20261101/native-v2';
const report=JSON.parse(readFileSync(join(DIR,'report.json')));
const clone=()=>structuredClone(report),word=n=>'0x'+BigInt(n).toString(16).padStart(64,'0');
test('actual recursive/physical adapter and24ordered native calls retain pending full gate',()=>{
 validateRecursiveReport(report,DIR);const ledger=validateRecursiveLedger();assert.equal(ledger.facts.length,18);assert.equal(ledger.obligations.length,24);assert.equal(ledger.combinations.length,6);assert.equal(report.rows.length,4);assert.equal(report.rows.reduce((n,r)=>n+r.calls.length,0),24);verifyRecursiveInputs('/workspace/vy5-dependencies-20261101');
});
for(const key of Object.keys(report.model))test('missing/malformed model '+key+' fails closed',()=>{
 const x=structuredClone(report.model);delete x[key];assert.throws(()=>validateRecursiveModel(x));
 const y=structuredClone(report.model);y[key]=null;assert.throws(()=>validateRecursiveModel(y));
});
const modelMutants={
 'cleaned bool with equal logical truth':m=>m.cells[0]='1',
 'truncated uint8':m=>m.cells[3]='1',
 'cleaned function address':m=>m.cells[1]=(2n**160n-1n).toString(),
 'cleaned function selector':m=>m.cells[5]=(2n**32n-1n).toString(),
 'aliased same-type function address':m=>m.cells[4]=m.cells[1],
 'aliased same-type function selector':m=>m.cells[2]=m.cells[5],
 'wrong packed byte orientation':m=>m.cells[6]='171',
 'overwritten nonword':m=>m.nonwordId=9,
 'overwritten source heap':m=>m.heapBytes=[170,0],
 'overwritten source logs':m=>m.sourceLogs=[],
 'lost physical padding':m=>m.physical.first='2',
 'lost physical owned byte':m=>m.physical.first=String(0xab000001),
 'lost outer rollback':m=>m.physical.outer=m.physical.child,
 'wrong physical owner':m=>m.wrongOwner=true,
 'wrong physical slot':m=>m.wrongSlot=true,
 'wrong target byte window':m=>m.targetBytes=[238,170,238],
 'unproved clean resumption':m=>m.cleanBridgeAccepted=true,
 'raw resume accepted':m=>m.rawResumeRefused=false,
 'missing decrement falsely complete':m=>m.divergentHorizons[6].exhausted=false,
 'wrong function arity':m=>m.arities[0]=[1,1],
 'reordered horizons':m=>m.horizons.reverse(),
 'dropped horizon':m=>m.horizons.pop(),
 'exhaustion relabelled complete':m=>m.horizons[0].outcome=m.horizons[6].outcome,
 'static error relabelled exhaustion':m=>m.staticHorizons[0].outcome={tag:'exhausted'},
 'static error still executes local block':m=>m.staticHorizons[6].outcome=m.horizons[6].outcome
};
for(const [name,mutate]of Object.entries(modelMutants))test(name+' rejected independently of return bytes',()=>{const x=structuredClone(report.model);mutate(x);assert.throws(()=>validateRecursiveModel(x));});
const mutants={
 'missing profile':r=>r.rows.pop(),
 'reordered profiles':r=>r.rows.reverse(),
 'wrong pipeline identity':r=>r.rows[0].pipeline='viaIR',
 'wrong optimizer':r=>r.rows[0].optimized=true,
 'missing call':r=>r.rows[0].calls.pop(),
 'reordered identical signatures':r=>{const a=r.rows[0].calls;[a[0],a[2]]=[a[2],a[0]];},
 'wrong selector request':r=>r.rows[0].calls[1].capture.request.input='0x',
 'wrong request ordinal':r=>r.rows[0].calls[1].capture.transaction=9,
 'wrong root owner':r=>r.rows[0].calls[1].capture.frames[0].address='0x'+'34'.repeat(20),
 'wrong child caller':r=>r.rows[0].calls[4].capture.frames[1].caller='0x'+'34'.repeat(20),
 'wrong child function':r=>r.rows[0].calls[4].capture.frames[1].input='0x',
 'missing child frame':r=>r.rows[0].calls[4].capture.frames.pop(),
 'lost rollback equal return':r=>r.rows[0].calls[4].capture.post[r.rows[0].address].persistent[word(43)]=word(0xcd000003),
 'wrong storage equal return':r=>r.rows[0].calls[1].capture.post[r.rows[0].address].persistent[word(43)]=word(0xab000001),
 'wrong unused slot equal return':r=>r.rows[0].calls[1].capture.post[r.rows[0].address].persistent[word(42)]=word(1),
 'missing state evidence':r=>delete r.rows[0].calls[1].capture.post[r.rows[0].address].persistent[word(43)],
 'unrelated pre state':r=>r.rows[0].calls[4].capture.pre[r.rows[0].address].persistent[word(43)]=word(0),
 'wrong balance':r=>r.rows[0].calls[1].capture.post[r.rows[0].address].balance='1',
 'wrong caller nonce':r=>r.rows[0].calls[1].capture.post[r.rows[0].calls[1].capture.request.caller].nonce='99',
 'missing memory region':r=>r.rows[0].calls[1].capture.frames[0].regions=[],
 'wrong output-memory bytes equal returns':r=>{const w=r.rows[0].calls[1].capture.frames[0].regions.find(x=>x.opcode==='RETURN');const i=Number(w.offset)*2+2;w.bytes=w.bytes.slice(0,i)+'01'+w.bytes.slice(i+2);},
 'wrong output-memory length':r=>r.rows[0].calls[1].capture.frames[0].regions.find(x=>x.opcode==='RETURN').length='32',
 'wrong create identity':r=>r.rows[0].deployment.capture.frames[0].createdAddress='0x'+'34'.repeat(20),
 'wrong installed code':r=>r.rows[0].deployment.capture.post[r.rows[0].address].code='0x',
 'missing producer receipt hash':r=>delete r.inputHashes['tests/yul-composition/local-producer-input.json'],
 'stale oracle hash':r=>r.inputHashes['tests/yul-composition/function-expectations.json']='0'.repeat(64),
 'stale source hash':r=>r.inputHashes['tests/yul-composition/RecursivePhysicalControls.sol']='0'.repeat(64),
 'stale runner hash':r=>r.runnerSha256='0'.repeat(64),
 'stale proof body':r=>r.consumerHashes[Object.keys(r.consumerHashes)[0]]='0'.repeat(64),
 'false full proof closure':r=>r.fullProofGate='pass'
};
for(const [name,change]of Object.entries(mutants))test(name+' fails closed',()=>{const x=clone();change(x);assert.throws(()=>validateRecursiveReport(x,DIR));});
test('current source/receipt/oracle files are checked, not just declared report hashes',()=>{
 for(const file of Object.keys(report.inputHashes))for(const missing of [false,true]){
  const original=fs.readFileSync,absolute=resolve(file);
  fs.readFileSync=function(path,...args){if(String(path)===absolute){if(missing)throw Error('ENOENT '+file);return Buffer.from('stale file bytes');}return original.call(fs,path,...args);};syncBuiltinESMExports();
  try{assert.throws(()=>validateRecursiveReport(report,DIR));}finally{fs.readFileSync=original;syncBuiltinESMExports();}
 }
});
test('producer omission, source hash and semantic hold cannot drift',()=>{
 const bytes=readFileSync('tests/yul-composition/local-producer-input.json');validateRecursiveInput(bytes);
 for(const change of [r=>r.modules.pop(),r=>r.head='0'.repeat(40),r=>r.modules[0].sha256='0'.repeat(64)]){const r=JSON.parse(bytes);change(r);assert.throws(()=>validateRecursiveInput(Buffer.from(JSON.stringify(r))));}
});
test('missing proof facts and false24/six closure cannot pass',()=>{
 const bytes=readFileSync('tests/yul-composition/recursive-component-ledger.json');validateRecursiveLedger(bytes);
 for(const change of [r=>r.facts.pop(),r=>r.sourceHashes={},r=>r.fullObligationsClosed=24,r=>r.obligations[0].status='done',r=>r.combinations[0].status='done']){const r=JSON.parse(bytes);change(r);assert.throws(()=>validateRecursiveLedger(Buffer.from(JSON.stringify(r))));}
});
test('actual Lean outputs/exit metadata cannot be missing, changed or failed',()=>{
 const temp=mkdtempSync(join(tmpdir(),'vy5-local-'));
 try{for(const file of ['lean.stdout','lean.stderr','lean.execution.json'])copyFileSync(join(DIR,file),join(temp,file));
  for(const [file,value]of [['lean.stdout','{}'],['lean.stderr','error'],['lean.execution.json','{}']]){writeFileSync(join(temp,file),value);assert.throws(()=>validateRecursiveReport(report,temp));copyFileSync(join(DIR,file),join(temp,file));}
  rmSync(join(temp,'lean.stdout'));assert.throws(()=>validateRecursiveReport(report,temp));
 }finally{rmSync(temp,{recursive:true,force:true});}
});

test('actual private producer/consumer body drift fails closed',()=>{
 for(const file of ['Solidity/Yul/LocalBlock.lean','Solidity/Yul/Composition/RecursivePhysical.lean']){
  const original=fs.readFileSync,absolute='/workspace/vy5-dependencies-20261101/'+file;
  fs.readFileSync=function(path,...args){if(String(path)===absolute)return Buffer.from('stale actual producer body');return original.call(fs,path,...args);};syncBuiltinESMExports();
  try{assert.throws(()=>validateRecursiveReport(report,DIR));}finally{fs.readFileSync=original;syncBuiltinESMExports();}
 }
});

test('both physical journals and function arity/result controls remain discriminating',()=>{
 for(const [key,value]of Object.entries(report.model.journalLengths)){const x=structuredClone(report.model);x.journalLengths[key]=value+1;assert.throws(()=>validateRecursiveModel(x));}
 const x=structuredClone(report.model);x.arities[0]=[2,2];assert.throws(()=>validateRecursiveModel(x));
});
test('selected required function catalog cannot silently disappear',()=>{
 const original=fs.readFileSync,absolute=resolve('tests/yul-composition/ledger.json'),bytes=original(absolute),root=JSON.parse(bytes);delete root.functionComponentEvidence;
 fs.readFileSync=function(path,...args){if(String(path)===absolute)return Buffer.from(JSON.stringify(root));return original.call(fs,path,...args);};syncBuiltinESMExports();
 try{assert.throws(()=>validateRecursiveReport(report,DIR));}finally{fs.readFileSync=original;syncBuiltinESMExports();}
});

test('actual imported FunctionPhysical private body drift is rejected',()=>{
 const original=fs.readFileSync;
 try {fs.readFileSync=function(path,...args){const data=original.call(this,path,...args);if(String(path)==='/workspace/vy5-dependencies-20261101/Solidity/Yul/Composition/FunctionPhysical.lean')return typeof data==='string'?data+'\n':Buffer.concat([data,Buffer.from('\n')]);return data;};syncBuiltinESMExports();assert.throws(()=>verifyRecursiveInputs('/workspace/vy5-dependencies-20261101'));}
 finally{fs.readFileSync=original;syncBuiltinESMExports();}
});

test('selected recursive catalog cannot disappear',()=>{
 const original=fs.readFileSync,absolute=resolve('tests/yul-composition/ledger.json'),root=JSON.parse(original(absolute));delete root.recursiveComponentEvidence;
 try{fs.readFileSync=function(path,...args){return String(path)===absolute?Buffer.from(JSON.stringify(root)):original.call(this,path,...args);};syncBuiltinESMExports();assert.throws(()=>validateRecursiveReport(report,DIR));}finally{fs.readFileSync=original;syncBuiltinESMExports();}
});
