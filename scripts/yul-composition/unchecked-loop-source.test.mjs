import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {join} from 'node:path';
import {ROOT} from './harness.mjs';
import {verifyUncheckedInputs,expectedUncheckedModel,validateUncheckedModel,validateUncheckedReport} from './unchecked-loop-source.mjs';
const clone=x=>structuredClone(x);
test('exact current private/producer/owned source registration',()=>assert.equal(Object.keys(verifyUncheckedInputs()).length,4));
test('independent complete selected Source oracle',()=>assert.deepEqual(validateUncheckedModel(expectedUncheckedModel()),{sourcePipelines:2,sourceCases:44,nativeComparisons:0,fullProofGate:'pending'}));
const mutations={
 'missing pipeline':m=>m.profiles.pop(), 'pipeline order':m=>m.profiles.reverse(),
 'missing call':m=>m.profiles[0].cases.pop(), 'case order':m=>m.profiles[0].cases.reverse(),
 'wrong full same-length revert bytes':m=>m.profiles[0].cases[0].result.bytes=[170,187],
 'wrong old alias':m=>m.profiles[0].cases[3].result.bytes=[222,173],
 'normal rest skipped':m=>m.profiles[0].cases[4].result.bytes=[222,173],
 'false branch mislabelled':m=>m.profiles[0].cases[13].result={tag:'revert',bytes:[222,173]},
 'continue silently succeeds':m=>m.profiles[0].cases[15].result={tag:'success'},
 'dangling memory swallowed':m=>m.profiles[0].cases.at(-1).result={tag:'success'},
 'lost panic tail':m=>m.profiles[0].cases[2].result.bytes.pop(),
 'dirty word cleaned':m=>m.profiles[0].cases[0].after.raw[0]='1',
 'raw input reset':m=>m.profiles[0].cases[0].after.raw[3]='1',
 'nonword alias overwritten':m=>m.profiles[0].cases[0].after.alias.bytes=[222,173],
 'heap payload overwritten':m=>m.profiles[0].cases[0].after.object.bytes=[170,187],
 'fnLocals overwritten':m=>m.profiles[0].cases[0].after.frame.types=['bool'],
 'caller locals not restored':m=>m.profiles[0].cases[0].outerRef.logicalIndex=1,
 'prefix log lost':m=>m.profiles[0].cases[0].after.logs=[],
 'wrong represented slot':m=>m.profiles[0].cases[0].physicalAfter.residualJournal[0][2]='44',
 'wrong owner':m=>m.profiles[0].cases[0].physicalAfter.ownedJournal[0][1]='2',
 'lost high physical bits':m=>m.profiles[0].cases[0].physicalAfter.word='2',
 'lost actual source journal':m=>m.profiles[0].cases[0].physicalAfter.sourceJournalLength=0,
 'lost residual journal':m=>m.profiles[0].cases[0].physicalAfter.residualJournal=[],
 'lost owned journal':m=>m.profiles[0].cases[0].physicalAfter.ownedJournal=[],
 'fake new native observation':m=>m.nativeComparisons=1,
 'fake full proof':m=>m.fullProofGate='pass',
 'missing before evidence':m=>delete m.profiles[0].cases[0].before,
 'unexpected extra observation':m=>m.profiles[0].cases[0].extra='unvalidated'
};
for(const[name,change]of Object.entries(mutations))test(name,()=>{const m=clone(expectedUncheckedModel());change(m);assert.throws(()=>validateUncheckedModel(m));});
for(const target of ['Solidity/Yul/Composition/UncheckedLoopPhysical.lean','tests/yul-composition/UncheckedLoopDriver.lean','tests/yul-composition/unchecked-loop-expectations.json','tests/yul-composition/unchecked-loop-ledger.json'])test('stale '+target,()=>assert.throws(()=>verifyUncheckedInputs(name=>{const bytes=readFileSync(join(ROOT,name));return name===target?Buffer.concat([bytes,Buffer.from(' drift')]):bytes;})));
test('missing selected registration',()=>assert.throws(()=>verifyUncheckedInputs(name=>{if(name==='tests/yul-composition/ledger.json'){const l=JSON.parse(readFileSync(join(ROOT,name)));delete l.uncheckedLoopEvidence;return Buffer.from(JSON.stringify(l));}return readFileSync(join(ROOT,name));})));

const directory='/workspace/vy5-composition/unchecked-loop-20261102/readback-v1';
const report=JSON.parse(readFileSync(join(directory,'report.json')));
test('all44 actual Source executions and complete receipt replay',()=>assert.deepEqual(validateUncheckedReport(report,directory),{sourcePipelines:2,sourceCases:44,nativeComparisons:0,fullProofGate:'pending'}));
const badReports={
 'wrong command':r=>r.command[5]='-j2',
 'wrong dependency':r=>r.dependency='/tmp/other',
 'failed process':r=>r.exit=1,
 'stale source identity':r=>r.bindings['Solidity/Yul/Composition/UncheckedLoopPhysical.lean']='0'.repeat(64),
 'wrong stdout hash':r=>r.stdoutSha256='0'.repeat(64),
 'wrong stderr hash':r=>r.stderrSha256='0'.repeat(64),
 'dropped observed case':r=>r.model.profiles[0].cases.pop(),
 'wrong compared bytes':r=>r.model.profiles[0].cases[0].result.bytes=[170,187],
 'false summary':r=>r.summary.sourceCases=43,
 'invented proof':r=>r.summary.fullProofGate='pass',
 'extra unvalidated evidence':r=>r.extra=true,
 'missing model':r=>delete r.model
};
for(const[name,change]of Object.entries(badReports))test('report '+name,()=>{const r=clone(report);change(r);assert.throws(()=>validateUncheckedReport(r,directory));});
for(const target of ['execution.json','lean.stdout','lean.stderr','lean.exit'])test('missing actual '+target,()=>assert.throws(()=>validateUncheckedReport(report,directory,path=>{if(path.endsWith('/'+target))throw Error('missing evidence');return readFileSync(path,'utf8');})));
for(const target of ['execution.json','lean.stdout','lean.stderr','lean.exit'])test('malformed actual '+target,()=>assert.throws(()=>validateUncheckedReport(report,directory,path=>path.endsWith('/'+target)?'malformed':readFileSync(path,'utf8'))));
