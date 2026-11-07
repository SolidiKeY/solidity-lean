import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync,writeFileSync,mkdtempSync,copyFileSync,rmSync} from 'node:fs';
import {tmpdir} from 'node:os';
import {join} from 'node:path';
import {validateModel,validateInput,verifyPhysicalInputs,validatePhysicalLedger,validatePhysicalReport} from './physical-source.mjs';
const DIR=process.env.VY5_PHYSICAL_REPORT_DIR??'/workspace/vy5-composition/physical-source-20261101/native-v3';
const report=JSON.parse(readFileSync(join(DIR,'report.json')));
const clone=()=>structuredClone(report);
const word=n=>'0x'+BigInt(n).toString(16).padStart(64,'0');
test('actual represented source and four native profiles retain all32 ordered calls',()=>{
 validatePhysicalReport(report,DIR);assert.equal(report.rows.length,4);assert.equal(report.rows.reduce((n,r)=>n+r.calls.length,0),32);
 assert.equal(report.fullProofGate,'pending');verifyPhysicalInputs('/workspace/vy5-dependencies-20261101');
});
for(const key of Object.keys(report.model))test('missing/wrong actual model '+key,()=>{
 const x=structuredClone(report.model);delete x[key];assert.throws(()=>validateModel(x));
 const y=structuredClone(report.model);y[key]=null;assert.throws(()=>validateModel(y));
});
const changes={
 'missing profile':r=>r.rows.pop(),
 'reordered profiles':r=>r.rows.reverse(),
 'wrong optimizer':r=>r.rows[0].optimized=true,
 'missing call':r=>r.rows[0].calls.pop(),
 'reordered calls':r=>r.rows[0].calls.reverse(),
 'wrong signature':r=>r.rows[0].calls[0].signature='child()',
 'wrong call identity':r=>r.rows[0].calls[0].capture.request.input='0x',
 'wrong caller':r=>r.rows[0].calls[0].capture.frames[0].caller='0x'+'34'.repeat(20),
 'wrong account':r=>r.rows[0].calls[0].capture.frames[0].address='0x'+'34'.repeat(20),
 'missing frame':r=>r.rows[0].calls[1].capture.frames.pop(),
 'wrong child caller':r=>r.rows[0].calls[1].capture.frames[1].caller='0x'+'34'.repeat(20),
 'wrong child input':r=>r.rows[0].calls[1].capture.frames[1].input='0x',
 'wrong child static':r=>r.rows[0].calls[1].capture.frames[1].isStatic=true,
 'wrong child slot':r=>r.rows[0].calls[1].capture.operations.find(o=>o.kind==='putStorage').slot=word(42),
 'lost rollback':r=>r.rows[0].calls[1].capture.post[r.rows[0].address].persistent[word(43)]=word(0xcd000003),
 'lost raw owned byte':r=>r.rows[0].calls[3].capture.post[r.rows[0].address].persistent[word(43)]=word(0xab000001),
 'lost raw padding':r=>r.rows[0].calls[3].capture.post[r.rows[0].address].persistent[word(43)]=word(2),
 'wrong untouched slot':r=>r.rows[0].calls[3].capture.post[r.rows[0].address].persistent[word(42)]=word(1),
 'missing slot':r=>delete r.rows[0].calls[3].capture.post[r.rows[0].address].persistent[word(43)],
 'wrong pre state equal post':r=>r.rows[0].calls[1].capture.pre[r.rows[0].address].persistent[word(43)]=word(2),
 'wrong caller nonce':r=>r.rows[0].calls[1].capture.post[r.rows[0].calls[1].capture.request.caller].nonce='9',
 'wrong balance equal returns':r=>r.rows[0].calls[3].capture.post[r.rows[0].address].balance='1',
 'wrong runtime':r=>r.rows[0].calls[3].capture.post[r.rows[0].address].code='0x',
 'missing semantic memory region':r=>r.rows[0].calls[0].capture.frames[0].regions=[],
 'wrong semantic memory byte':r=>{const w=r.rows[0].calls[0].capture.frames[0].regions.find(x=>x.opcode==='RETURN');const i=Number(w.offset)*2+2;w.bytes=w.bytes.slice(0,i)+'01'+w.bytes.slice(i+2);},
 'wrong memory length':r=>r.rows[0].calls[0].capture.frames[0].regions.find(x=>x.opcode==='RETURN').length='32',
 'wrong creation address':r=>r.rows[0].deployment.capture.frames[0].createdAddress='0x'+'34'.repeat(20),
 'missing installed code':r=>r.rows[0].deployment.capture.post[r.rows[0].address].code='0x',
 'stale source':r=>r.sourceSha256='0'.repeat(64),
 'stale producer':r=>r.producerInputSha256='0'.repeat(64),
 'stale oracle call plan':r=>r.callPlanSha256='0'.repeat(64),
 'stale runner':r=>r.runnerSha256='0'.repeat(64),
 'stale ledger':r=>r.physicalLedgerSha256='0'.repeat(64),
 'stale consumer':r=>r.consumerHashes[Object.keys(r.consumerHashes)[0]]='0'.repeat(64),
 'false full proof':r=>r.fullProofGate='pass',
 'wrong source static projection':r=>r.model.staticRaw=0xcd000003,
 'wrong target copied byte':r=>r.model.copied[1]=0,
 'wrong allocation payload':r=>r.model.allocations[1].payload=[0]
};
for(const [name,change]of Object.entries(changes))test(name+' fails closed',()=>{const x=clone();change(x);assert.throws(()=>validatePhysicalReport(x,DIR));});
test('producer omissions and stale hashes fail closed',()=>{
 const bytes=readFileSync('tests/yul-composition/physical-producer-input.json');validateInput(bytes);
 for(const change of [r=>r.modules.pop(),r=>r.modules[0].sha256='0'.repeat(64),r=>r.head='0'.repeat(40)]){const r=JSON.parse(bytes);change(r);assert.throws(()=>validateInput(Buffer.from(JSON.stringify(r))));}
});
test('missing facts, stale source or false ledger closure fail closed',()=>{
 const bytes=readFileSync('tests/yul-composition/physical-component-ledger.json');validatePhysicalLedger(bytes);
 for(const change of [r=>r.facts.pop(),r=>r.sourceHashes={},r=>r.obligations[0].status='done',r=>r.combinations[0].status='done',r=>r.fullObligationsClosed=24]){const r=JSON.parse(bytes);change(r);assert.throws(()=>validatePhysicalLedger(Buffer.from(JSON.stringify(r))));}
});
test('retained actual Lean execution cannot be missing/replaced/failed',()=>{
 const temp=mkdtempSync(join(tmpdir(),'vy5-physical-'));
 try{
  for(const file of ['lean.stdout','lean.stderr','lean.execution.json'])copyFileSync(join(DIR,file),join(temp,file));
  for(const [file,wrong]of [['lean.stdout','{}'],['lean.stderr','failure'],['lean.execution.json','{}']]){
   writeFileSync(join(temp,file),wrong);assert.throws(()=>validatePhysicalReport(report,temp));copyFileSync(join(DIR,file),join(temp,file));
  }
  rmSync(join(temp,'lean.stdout'));assert.throws(()=>validatePhysicalReport(report,temp));
 }finally{rmSync(temp,{recursive:true,force:true});}
});
