import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {validateLean,compareProjection,verifyInputs,verifyProducerReceipt,validateComponentLedger,validateComponentReport} from './component.mjs';
import {predictedAliases} from './oracles.mjs';
const ROOT=process.env.VY5_COMPONENT_REPORT_DIR??'/workspace/vy5-composition/physical-source-20261101/old-components';
const report=JSON.parse(readFileSync(ROOT+'/report.json'));
const lean=report.lean;
test('actual component evidence matches independently stated finite outcomes',()=>{
 validateLean(lean);assert.equal(report.rows.length,4);for(const r of report.rows)assert.equal(compareProjection(lean,r.actual),'match');assert.equal(report.target.status,'match');
});
test('missing/malformed/wrong actual Lean outputs fail closed',()=>{
 for(const key of Object.keys(lean)){const x=structuredClone(lean);delete x[key];assert.throws(()=>validateLean(x));}
 for(const key of ['word','scope','repeat','revert','success','code']){const x=structuredClone(lean);x[key][0]++;assert.throws(()=>validateLean(x));}
 assert.throws(()=>validateLean({...lean,extra:true}));
});
test('equal returns cannot mask wrong storage, owner or ordered log bytes',()=>{
 const a=report.rows[0].actual;
 for(const change of [x=>x.storage='0x'+'00'.repeat(32),x=>x.logs[0].data='0x12',x=>x.logs.push(structuredClone(x.logs[0])),x=>x.logs[0].topics=['0x'+'00'.repeat(32)],x=>x.failed=true,x=>x.pairResult.failed=true,x=>x.pairResult.exception='revert',x=>x.pairResult.logs.push({emitter:x.address,topics:[],data:'0x11'}),x=>x.bytes='0xcdab',x=>x.pair='0x'+'00'.repeat(32)]){const x=structuredClone(a);change(x);assert.equal(compareProjection(lean,x),'mismatch');}
 const x=structuredClone(a);x.address='0x'+'34'.repeat(20);x.logs[0].emitter=x.address;assert.throws(()=>compareProjection(lean,x));
 for(const key of ['storage','logs','address','bytes','pair','failed']){const x=structuredClone(a);delete x[key];if(['logs','address'].includes(key))assert.throws(()=>compareProjection(lean,x));else assert.equal(compareProjection(lean,x),'mismatch');}
 assert.equal(a.address,predictedAliases().self);
});
test('actual peer and own bodies agree with pinned source receipts',()=>{
 const x=verifyInputs('/workspace/vy5-dependencies-20261101');assert.equal(Object.keys(x.consumerHashes).length,7);assert.equal(x.producerInputsSha256.length,64);
});

test('producer registry omissions, duplicates and wrong identities fail closed',()=>{
 const bytes=readFileSync('tests/yul-composition/producer-inputs.json');verifyProducerReceipt(bytes);
 const base=JSON.parse(bytes);
 for(const change of [x=>x.packages=[],x=>x.packages.push(x.packages[0]),x=>x.packages[0].modules=[],x=>x.packages[0].modules.pop(),x=>x.packages[0].head='0'.repeat(40),x=>x.packages[0].base='0'.repeat(40),x=>x.packages[0].producer='other',x=>x.packages[0].modules[0].sha256='0'.repeat(64)]){const x=structuredClone(base);change(x);assert.throws(()=>verifyProducerReceipt(Buffer.from(JSON.stringify(x))));}
});

test('component facts never discharge original obligations or accept stale/missing proof evidence',()=>{
 const r=JSON.parse(readFileSync('tests/yul-composition/component-ledger.json'));validateComponentLedger(r);
 for(const change of [x=>x.facts.pop(),x=>x.facts[0].module='Solidity/Yul/Composition/Interface.lean',x=>x.obligations[0].dependencies=[],x=>x.combinations[0].required=[],x=>x.obligations[0].owner='VY5',x=>x.facts[1]=x.facts[0],x=>x.fullObligationsClosed=1,x=>x.obligations.pop(),x=>x.combinations.pop(),x=>x.obligations[0].fullStatus='done',x=>x.producerHeads.reverse(),x=>delete x.consumerModuleHashes['Solidity/Yul/Composition/Interface.lean'],x=>x.consumerModuleHashes['Solidity/Yul/Composition/Concrete.lean']='0'.repeat(64)]){const x=structuredClone(r);change(x);assert.throws(()=>validateComponentLedger(x));}
});

test('actual reports reject missing/reordered frames/profiles and stale requests/receipts',()=>{
 validateComponentReport(report,ROOT);
 for(const change of [x=>delete x.consumerHashes['Solidity/Yul/Composition/Concrete.lean'],x=>x.rows.reverse(),x=>x.rows.pop(),x=>x.rows[0].receipt.inputSha256='0'.repeat(64),x=>x.sourceSha256='0'.repeat(64),x=>x.rows[0].pairCapture.frames=[],x=>x.rows[0].pairCapture.request.input='0xdeadbeef',x=>x.rows[0].caughtCapture.frames.reverse(),x=>x.target.code='5f5ffd',x=>x.target.runtimeSha256='0'.repeat(64),x=>delete x.target.capture]){const x=structuredClone(report);change(x);assert.throws(()=>validateComponentReport(x,ROOT));}
});

test('coordinated same-runtime deployment failures/logs/data cannot pass report validation',()=>{
 for(const change of [x=>{x.target.deploymentResult.failed=true;x.target.deploymentResult.exception='revert';x.target.deploymentCapture.frames[0].output.exception='revert';},x=>{const l={emitter:predictedAliases().self,topics:[],data:'0x11'};x.target.deploymentResult.logs=[l];x.target.deploymentCapture.frames[0].output.logs=[l];},x=>{x.target.deploymentResult.returnData='0xdead';x.target.deploymentCapture.frames[0].output.bytes='0xdead';}]){const x=structuredClone(report);change(x);assert.throws(()=>validateComponentReport(x,ROOT));}
});

test('fixed caller/value and required nested/ready-fact evidence cannot be coordinated away',()=>{
 for(const change of [x=>x.readyComponentFacts=[],x=>x.rows[0].internalWrite42=false,x=>x.rows[0].caughtCapture.operations=x.rows[0].caughtCapture.operations.filter(o=>o.kind!=='putStorage'),x=>{for(const c of [x.rows[0].deployment,x.rows[0].pairCapture,x.rows[0].caughtCapture,x.target.deploymentCapture,x.target.capture]){c.request.caller='0x'+'34'.repeat(20);c.frames[0].caller=c.request.caller;}},x=>{x.rows[0].pairCapture.request.value='1';x.rows[0].pairCapture.frames[0].value='1';}]){const x=structuredClone(report);change(x);assert.throws(()=>validateComponentReport(x,ROOT));}
});
