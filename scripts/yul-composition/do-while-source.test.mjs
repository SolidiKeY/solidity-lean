import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {join} from 'node:path';
import {ROOT} from './harness.mjs';
import {verifyDoWhileInputs,expectedDoWhileModel,validateDoWhileModel,validateDoWhileReport} from './do-while-source.mjs';
const clone=x=>structuredClone(x);
test('exact owned/private/producer/runner registration',()=>assert.equal(Object.keys(verifyDoWhileInputs()).length,5));
test('independent full selected Source doWhile oracle',()=>assert.deepEqual(validateDoWhileModel(expectedDoWhileModel()),{sourcePipelines:2,sourceCases:50,nativeComparisons:0,fullProofGate:'pending'}));
const mutations={
 'missing pipeline':m=>m.profiles.pop(), 'pipeline order':m=>m.profiles.reverse(),
 'missing case':m=>m.profiles[0].cases.pop(), 'case order':m=>m.profiles[0].cases.reverse(),
 'same-length wrong revert bytes':m=>m.profiles[0].cases[0].result.bytes=[170,187],
 'wrong alias ignored':m=>m.profiles[0].cases[3].result.bytes=[222,173],
 'lost full panic tail':m=>m.profiles[0].cases[2].result.bytes.pop(),
 'body incorrectly skipped for false condition':m=>m.profiles[0].cases[0].result={tag:'success',flow:'normal',locals:[]},
 'revert evaluates poison condition':m=>m.profiles[0].cases[4].result.bytes=[1],
 'break evaluates poison':m=>m.profiles[0].cases[5].result={tag:'timeout'},
 'continue skips actual assignment':m=>m.profiles[0].cases[6].result.locals[0].value=true,
 'normal fails to restore declaration scope':m=>m.profiles[0].cases[7].result.locals.unshift({type:'bool',value:true}),
 'normal assigns shadow instead of caller':m=>m.profiles[0].cases[7].result.locals[0].value=true,
 'continue false treated as break':m=>m.profiles[0].cases[8].result.flow='break',
 'return consumed as normal':m=>m.profiles[0].cases[9].result.flow='normal',
 'truecontinue incorrectly terminates':m=>m.profiles[0].cases[10].result={tag:'success',flow:'normal',locals:[]},
 'poison condition not evaluated':m=>m.profiles[0].cases[11].result.bytes[35]=1,
 'normal poison condition swallowed':m=>m.profiles[0].cases[12].result={tag:'timeout'},
 'revert executes outside rest':m=>m.profiles[0].cases[13].result.bytes=[170,187],
 'break skips outside rest':m=>m.profiles[0].cases[14].result={tag:'success',flow:'normal',locals:[]},
 'low fuel falsely completes':m=>m.profiles[0].cases[19].result={tag:'revert',bytes:[222,173]},
 'pending timeout loses caller state':m=>m.profiles[0].cases[22].after.next=0,
 'dangling swallowed':m=>m.profiles[0].cases[23].result={tag:'revert',bytes:[]},
 'break evaluates dangling condition':m=>m.profiles[0].cases[24].result={tag:'stuck',reason:'dangling memory reference'},
 'wrong retained local reference':m=>m.profiles[0].cases[6].result.locals[1].logicalIndex=0,
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
for(const[name,change]of Object.entries(mutations))test(name,()=>{const m=clone(expectedDoWhileModel());change(m);assert.throws(()=>validateDoWhileModel(m));});
for(const target of ['Solidity/Yul/Composition/DoWhilePhysical.lean','tests/yul-composition/DoWhileDriver.lean','tests/yul-composition/do-while-expectations.json','tests/yul-composition/do-while-ledger.json'])test('stale '+target,()=>assert.throws(()=>verifyDoWhileInputs(name=>{const bytes=readFileSync(join(ROOT,name));return name===target?Buffer.concat([bytes,Buffer.from(' drift')]):bytes;})));
test('missing selected registration',()=>assert.throws(()=>verifyDoWhileInputs(name=>{if(name==='tests/yul-composition/ledger.json'){const l=JSON.parse(readFileSync(join(ROOT,name)));delete l.doWhileEvidence;return Buffer.from(JSON.stringify(l));}return readFileSync(join(ROOT,name));})));
const directory='/workspace/vy5-composition/do-while-20261102/readback-v1';
const report=JSON.parse(readFileSync(join(directory,'report.json')));
test('all50 actual Source executions and exact receipt replay',()=>assert.deepEqual(validateDoWhileReport(report,directory),{sourcePipelines:2,sourceCases:50,nativeComparisons:0,fullProofGate:'pending'}));
const badReports={
 'wrong command':r=>r.command[5]='-j2', 'wrong dependency':r=>r.dependency='/tmp/other', 'failed process':r=>r.exit=1,
 'stale source identity':r=>r.bindings['Solidity/Yul/Composition/DoWhilePhysical.lean']='0'.repeat(64),
 'stale runner identity':r=>r.bindings['scripts/yul-composition/do-while-source.mjs']='0'.repeat(64),
 'wrong stdout hash':r=>r.stdoutSha256='0'.repeat(64), 'wrong stderr hash':r=>r.stderrSha256='0'.repeat(64),
 'dropped actual case':r=>r.model.profiles[0].cases.pop(),
 'wrong actual bytes':r=>r.model.profiles[0].cases[0].result.bytes=[170,187],
 'false summary':r=>r.summary.sourceCases=49, 'invented proof':r=>r.summary.fullProofGate='pass',
 'extra unvalidated evidence':r=>r.extra=true, 'missing model':r=>delete r.model
};
for(const[name,change]of Object.entries(badReports))test('report '+name,()=>{const r=clone(report);change(r);assert.throws(()=>validateDoWhileReport(r,directory));});
for(const target of ['execution.json','lean.stdout','lean.stderr','lean.exit'])test('missing actual '+target,()=>assert.throws(()=>validateDoWhileReport(report,directory,path=>{if(path.endsWith('/'+target))throw Error('missing evidence');return readFileSync(path,'utf8');})));
for(const target of ['execution.json','lean.stdout','lean.stderr','lean.exit'])test('malformed actual '+target,()=>assert.throws(()=>validateDoWhileReport(report,directory,path=>path.endsWith('/'+target)?'malformed':readFileSync(path,'utf8'))));
