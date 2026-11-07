import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {join} from 'node:path';
import {ROOT} from './harness.mjs';
import {verifyForInputs,expectedForModel,validateForModel,validateForReport} from './for-source.mjs';
const clone=x=>structuredClone(x);
test('exact owned/private/producer/runner registration',()=>assert.equal(Object.keys(verifyForInputs()).length,5));
test('independent full selected Source for-loop oracle',()=>assert.deepEqual(validateForModel(expectedForModel()),{sourcePipelines:2,sourceCases:56,nativeComparisons:0,fullProofGate:'pending'}));
const mutations={
 'missing pipeline':m=>m.profiles.pop(), 'pipeline order':m=>m.profiles.reverse(),
 'missing case':m=>m.profiles[0].cases.pop(), 'case order':m=>m.profiles[0].cases.reverse(),
 'same-length wrong revert bytes':m=>m.profiles[0].cases[0].result.bytes=[170,187],
 'wrong alias ignored':m=>m.profiles[0].cases[3].result.bytes=[222,173],
 'lost full panic tail':m=>m.profiles[0].cases[2].result.bytes.pop(),
 'false condition ignored':m=>m.profiles[0].cases[4].result={tag:'revert',bytes:[222,173]},
 'break executes poison post':m=>m.profiles[0].cases[5].result={tag:'timeout'},
 'break executes body tail':m=>m.profiles[0].cases[6].result={tag:'revert',bytes:[222,173]},
 'continue skips caller bool update':m=>m.profiles[0].cases[7].result.locals[0].value=true,
 'continue omits next false test':m=>m.profiles[0].cases[7].result={tag:'timeout'},
 'missing post silently terminates':m=>m.profiles[0].cases[8].result={tag:'success',flow:'normal',locals:[]},
 'poison post not actually poison':m=>m.profiles[0].cases[9].result.bytes[35]=1,
 'break incorrectly skips outside rest':m=>m.profiles[0].cases[10].result={tag:'success',flow:'normal',locals:[]},
 'revert incorrectly runs outside rest':m=>m.profiles[0].cases[11].result.bytes=[170,187],
 'dangling reference swallowed':m=>m.profiles[0].cases[23].result={tag:'revert',bytes:[]},
 'invalid init accepted':m=>m.profiles[0].cases[24].result={tag:'success'},
 'false condition reads dangling body':m=>m.profiles[0].cases[25].result={tag:'stuck',reason:'dangling memory reference'},
 'init local not restored':m=>m.profiles[0].cases[4].result.locals.unshift({type:'bool',value:false}),
 'init false value wrong':m=>m.profiles[0].cases[27].result.locals[0].value=true,
 'caller flag cleared during init':m=>m.profiles[0].cases[26].result.locals[1].value=false,
 'wrong retained callee reference':m=>m.profiles[0].cases[7].result.locals[1].logicalIndex=0,
 'wrong input local scope':m=>m.profiles[0].cases[0].inputLocals.pop(),
 'raw dirty word cleaned':m=>m.profiles[0].cases[0].after.raw[0]='1',
 'clean bool post written into raw caller':m=>m.profiles[0].cases[7].after.raw[0]='0',
 'raw function cells aliased':m=>m.profiles[0].cases[0].after.raw[4]=m.profiles[0].cases[0].after.raw[1],
 'nonword alias overwritten':m=>m.profiles[0].cases[0].after.alias.bytes=[222,173],
 'heap payload overwritten':m=>m.profiles[0].cases[0].after.object.bytes=[170,187],
 'heap extent changed':m=>m.profiles[0].cases[0].after.next=1,
 'fnLocals overwritten':m=>m.profiles[0].cases[0].after.frame.types=['bool'],
 'outer EM locals not restored':m=>m.profiles[0].cases[0].outerRef.logicalIndex=1,
 'caller prefix lost':m=>m.profiles[0].cases[0].after.logs=[],
 'wrong physical slot':m=>m.profiles[0].cases[0].physicalAfter.residualJournal[0][2]='44',
 'wrong physical owner':m=>m.profiles[0].cases[0].physicalAfter.ownedJournal[0][1]='2',
 'lost physical high bits':m=>m.profiles[0].cases[0].physicalAfter.word='2',
 'lost source journal':m=>m.profiles[0].cases[0].physicalAfter.sourceJournalLength=0,
 'lost residual journal':m=>m.profiles[0].cases[0].physicalAfter.residualJournal=[],
 'wrong saved owned-byte journal':m=>m.profiles[0].cases[0].physicalAfter.ownedJournal[0][4]=2,
 'invented native comparison':m=>m.nativeComparisons=1,
 'invented full proof':m=>m.fullProofGate='pass',
 'missing before evidence':m=>delete m.profiles[0].cases[0].before,
 'extra unvalidated observation':m=>m.profiles[0].cases[0].extra=true
};
for(const[name,change]of Object.entries(mutations))test(name,()=>{const m=clone(expectedForModel());change(m);assert.throws(()=>validateForModel(m));});
for(const target of ['Solidity/Yul/Composition/ForPhysical.lean','tests/yul-composition/ForDriver.lean','tests/yul-composition/for-expectations.json','tests/yul-composition/for-ledger.json'])test('stale '+target,()=>assert.throws(()=>verifyForInputs(name=>{const bytes=readFileSync(join(ROOT,name));return name===target?Buffer.concat([bytes,Buffer.from(' drift')]):bytes;})));
test('missing selected registration',()=>assert.throws(()=>verifyForInputs(name=>{if(name==='tests/yul-composition/ledger.json'){const l=JSON.parse(readFileSync(join(ROOT,name)));delete l.forEvidence;return Buffer.from(JSON.stringify(l));}return readFileSync(join(ROOT,name));})));
const directory='/workspace/vy5-composition/for-loop-20261102/readback-v1';
const report=JSON.parse(readFileSync(join(directory,'report.json')));
test('all56 actual Source executions and exact receipt replay',()=>assert.deepEqual(validateForReport(report,directory),{sourcePipelines:2,sourceCases:56,nativeComparisons:0,fullProofGate:'pending'}));
const badReports={
 'wrong command':r=>r.command[5]='-j2', 'wrong dependency':r=>r.dependency='/tmp/other', 'failed process':r=>r.exit=1,
 'stale source identity':r=>r.bindings['Solidity/Yul/Composition/ForPhysical.lean']='0'.repeat(64),
 'stale runner identity':r=>r.bindings['scripts/yul-composition/for-source.mjs']='0'.repeat(64),
 'wrong stdout hash':r=>r.stdoutSha256='0'.repeat(64), 'wrong stderr hash':r=>r.stderrSha256='0'.repeat(64),
 'dropped actual case':r=>r.model.profiles[0].cases.pop(),
 'wrong actual bytes':r=>r.model.profiles[0].cases[0].result.bytes=[170,187],
 'false summary':r=>r.summary.sourceCases=55, 'invented proof':r=>r.summary.fullProofGate='pass',
 'extra unvalidated evidence':r=>r.extra=true, 'missing model':r=>delete r.model
};
for(const[name,change]of Object.entries(badReports))test('report '+name,()=>{const r=clone(report);change(r);assert.throws(()=>validateForReport(r,directory));});
for(const target of ['execution.json','lean.stdout','lean.stderr','lean.exit'])test('missing actual '+target,()=>assert.throws(()=>validateForReport(report,directory,path=>{if(path.endsWith('/'+target))throw Error('missing evidence');return readFileSync(path,'utf8');})));
for(const target of ['execution.json','lean.stdout','lean.stderr','lean.exit'])test('malformed actual '+target,()=>assert.throws(()=>validateForReport(report,directory,path=>path.endsWith('/'+target)?'malformed':readFileSync(path,'utf8'))));
