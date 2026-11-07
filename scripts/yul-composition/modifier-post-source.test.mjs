import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {join} from 'node:path';
import {ROOT} from './harness.mjs';
import {verifyModifierPostInputs,expectedModifierPostModel,validateModifierPostModel,validateModifierPostReport} from './modifier-post-source.mjs';
const clone=x=>structuredClone(x);
test('exact owned/private/producer/runner registration',()=>assert.equal(Object.keys(verifyModifierPostInputs()).length,6));
test('independent full selected Source modifier postlude oracle',()=>assert.deepEqual(validateModifierPostModel(expectedModifierPostModel()),{sourcePipelines:2,sourceCases:48,nativeComparisons:0,fullProofGate:'pending'}));
const mutations={
 'missing pipeline':m=>m.profiles.pop(),'reordered pipeline':m=>m.profiles.reverse(),
 'missing case':m=>m.profiles[0].cases.pop(),'reordered case':m=>m.profiles[0].cases.reverse(),
 'same-length wrong body payload':m=>m.profiles[0].cases[0].result.bytes=[170,187],
 'wrong alias ignored':m=>m.profiles[0].cases[3].result.bytes=[222,173],
 'lost full panic tail':m=>m.profiles[0].cases[2].result.bytes.pop(),
 'normal incorrectly skips postlude':m=>m.profiles[0].cases[4].result={tag:'success',locals:[]},
 'return incorrectly skips postlude':m=>m.profiles[0].cases[5].result={tag:'success',locals:[]},
 'wrong postlude reference':m=>m.profiles[0].cases[6].result.bytes=[170,187],
 'panic postlude shortened':m=>m.profiles[0].cases[7].result.bytes.pop(),
 'empty postlude padded':m=>m.profiles[0].cases[8].result.bytes=[0],
 'body reads unreachable dangling postlude':m=>m.profiles[0].cases[9].result={tag:'stuck',reason:'dangling memory reference'},
 'normal dangling swallowed':m=>m.profiles[0].cases[10].result={tag:'revert',bytes:[]},
 'return dangling swallowed':m=>m.profiles[0].cases[11].result={tag:'revert',bytes:[]},
 'empty modifier runs body':m=>m.profiles[0].cases[12].result={tag:'revert',bytes:[222,173]},
 'empty modifier reads dangling':m=>m.profiles[0].cases[13].result={tag:'stuck',reason:'dangling memory reference'},
 'missing body accepted':m=>m.profiles[0].cases[14].result={tag:'success',locals:[]},
 'wrong frame accepted':m=>m.profiles[0].cases[15].result={tag:'success',locals:[]},
 'late timeout incorrectly completed':m=>m.profiles[0].cases[23].result={tag:'revert',bytes:[222,173]},
 'pending timeout loses saved frame':m=>m.profiles[0].cases[23].after.frame.types=[],
 'saved bool becomes temporary frame':m=>m.profiles[0].cases[0].after.frame.types=['bytes.memory','bytes.memory'],
 'saved bool cleared':m=>m.profiles[0].cases[0].after.frame.bool=false,
 'returned locals swapped':m=>m.profiles[0].cases[12].result.locals.reverse(),
 'dangling local reset':m=>m.profiles[0].cases[13].result.locals[1].logicalIndex=0,
 'wrong input scope':m=>m.profiles[0].cases[0].inputLocals.pop(),
 'lost raw dirty bool':m=>m.profiles[0].cases[0].after.raw[0]='1',
 'raw function aliases conflated':m=>m.profiles[0].cases[0].after.raw[4]=m.profiles[0].cases[0].after.raw[1],
 'heap payload mutated with equal return':m=>m.profiles[0].cases[0].after.object.bytes=[170,187],
 'old nonword alias mutated':m=>m.profiles[0].cases[0].after.alias.bytes=[222,173],
 'heap extent changed':m=>m.profiles[0].cases[0].after.next=1,
 'outer EM scope not restored':m=>m.profiles[0].cases[0].outerRef.logicalIndex=1,
 'caller log prefix lost':m=>m.profiles[0].cases[0].after.logs=[],
 'ordered credits reversed':m=>m.profiles[0].cases[0].after.events.reverse(),
 'credit bytes/value wrong':m=>m.profiles[0].cases[0].after.events[1].value='9',
 'physical high bits lost':m=>m.profiles[0].cases[0].physicalAfter.word='2',
 'wrong physical owner':m=>m.profiles[0].cases[0].physicalAfter.ownedJournal[0][1]='2',
 'wrong physical slot':m=>m.profiles[0].cases[0].physicalAfter.residualJournal[0][2]='44',
 'lost owned saved byte':m=>m.profiles[0].cases[0].physicalAfter.ownedJournal[0][4]=2,
 'lost residual journal':m=>m.profiles[0].cases[0].physicalAfter.residualJournal=[],
 'lost source journal length':m=>m.profiles[0].cases[0].physicalAfter.sourceJournalLength=0,
 'same-length wrong source journal owner':m=>m.profiles[0].cases[0].physicalAfter.sourceJournal[0].address='2',
 'wrong old journal nonce':m=>m.profiles[0].cases[0].physicalAfter.sourceJournal[0].old.nonce=1,
 'wrong old journal c value':m=>m.profiles[0].cases[0].physicalAfter.sourceJournal[0].old.storage.cValue=true,
 'wrong current persistent state':m=>m.profiles[0].cases[0].physicalAfter.currentAccount.storage.cValue=false,
 'invented transient write':m=>m.profiles[0].cases[0].physicalAfter.currentTransient.cValue=true,
 'invented native comparison':m=>m.nativeComparisons=1,'invented full proof':m=>m.fullProofGate='pass',
 'missing before state':m=>delete m.profiles[0].cases[0].before,'extra unvalidated field':m=>m.profiles[0].cases[0].extra=true
};
for(const[name,change]of Object.entries(mutations))test(name,()=>{const m=clone(expectedModifierPostModel());change(m);assert.throws(()=>validateModifierPostModel(m));});
for(const target of ['Solidity/Yul/Composition/ModifierPostPhysical.lean','tests/yul-composition/ModifierPostDriver.lean','tests/yul-composition/modifier-post-expectations.json','tests/yul-composition/modifier-post-ledger.json','Solidity/Yul/Composition/ModifierPhysical.lean'])test('stale '+target,()=>assert.throws(()=>verifyModifierPostInputs(name=>{const bytes=readFileSync(join(ROOT,name));return name===target?Buffer.concat([bytes,Buffer.from(' drift')]):bytes;})));
test('missing selected registration',()=>assert.throws(()=>verifyModifierPostInputs(name=>{if(name==='tests/yul-composition/ledger.json'){const l=JSON.parse(readFileSync(join(ROOT,name)));delete l.modifierPostEvidence;return Buffer.from(JSON.stringify(l));}return readFileSync(join(ROOT,name));})));
const directory='/workspace/vy5-composition/modifier-post-20261102/readback-v2';
const report=JSON.parse(readFileSync(join(directory,'report.json')));
test('all48 actual Source executions and exact receipt replay',()=>assert.deepEqual(validateModifierPostReport(report,directory),{sourcePipelines:2,sourceCases:48,nativeComparisons:0,fullProofGate:'pending'}));
const badReports={
 'wrong command':r=>r.command[5]='-j2', 'wrong dependency':r=>r.dependency='/tmp/other', 'failed process':r=>r.exit=1,
 'stale source identity':r=>r.bindings['Solidity/Yul/Composition/ModifierPostPhysical.lean']='0'.repeat(64),
 'stale runner identity':r=>r.bindings['scripts/yul-composition/modifier-post-source.mjs']='0'.repeat(64),
 'wrong stdout hash':r=>r.stdoutSha256='0'.repeat(64), 'wrong stderr hash':r=>r.stderrSha256='0'.repeat(64),
 'dropped actual case':r=>r.model.profiles[0].cases.pop(),
 'wrong actual bytes':r=>r.model.profiles[0].cases[0].result.bytes=[170,187],
 'false summary':r=>r.summary.sourceCases=47, 'invented proof':r=>r.summary.fullProofGate='pass',
 'extra unvalidated evidence':r=>r.extra=true, 'missing model':r=>delete r.model
};
for(const[name,change]of Object.entries(badReports))test('report '+name,()=>{const r=clone(report);change(r);assert.throws(()=>validateModifierPostReport(r,directory));});
for(const target of ['execution.json','lean.stdout','lean.stderr','lean.exit'])test('missing actual '+target,()=>assert.throws(()=>validateModifierPostReport(report,directory,path=>{if(path.endsWith('/'+target))throw Error('missing evidence');return readFileSync(path,'utf8');})));
for(const target of ['execution.json','lean.stdout','lean.stderr','lean.exit'])test('malformed actual '+target,()=>assert.throws(()=>validateModifierPostReport(report,directory,path=>path.endsWith('/'+target)?'malformed':readFileSync(path,'utf8'))));
