import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {join} from 'node:path';
import {ROOT} from './harness.mjs';
import {verifyNestedModifierInputs,expectedNestedModifierModel,validateNestedModifierModel,validateNestedModifierReport} from './nested-modifier-source.mjs';
const clone=x=>structuredClone(x);
test('exact owned/private/producer/runner registration',()=>assert.equal(Object.keys(verifyNestedModifierInputs()).length,5));
test('independent full selected Source nested modifier oracle',()=>assert.deepEqual(validateNestedModifierModel(expectedNestedModifierModel()),{sourcePipelines:2,sourceCases:78,nativeComparisons:0,fullProofGate:'pending'}));
const mutations={
 'missing pipeline':m=>m.profiles.pop(),'pipeline order':m=>m.profiles.reverse(),
 'missing case':m=>m.profiles[0].cases.pop(),'case order':m=>m.profiles[0].cases.reverse(),
 'same-length wrong body payload':m=>m.profiles[0].cases[0].result.bytes=[170,187],
 'body wrong alias ignored':m=>m.profiles[0].cases[3].result.bytes=[222,173],
 'lost panic tail':m=>m.profiles[0].cases[2].result.bytes.pop(),
 'normal executes outer instead of inner postlude':m=>m.profiles[0].cases[4].result.bytes=[222,173],
 'return skips inner postlude':m=>m.profiles[0].cases[5].result={tag:'success',locals:[]},
 'inner argument selection collapsed':m=>m.profiles[0].cases[6].result.bytes=[170,187],
 'modifier order ignored':m=>m.profiles[0].cases[7].result.bytes=[170,187],
 'unreachable dangling outer read':m=>m.profiles[0].cases[8].result={tag:'stuck',reason:'dangling memory reference'},
 'body failure reads unreachable dangling inner':m=>m.profiles[0].cases[9].result={tag:'stuck',reason:'dangling memory reference'},
 'normal ignores dangling inner':m=>m.profiles[0].cases[10].result={tag:'revert',bytes:[]},
 'return ignores dangling inner':m=>m.profiles[0].cases[11].result={tag:'revert',bytes:[]},
 'empty outer executes body':m=>m.profiles[0].cases[12].result={tag:'revert',bytes:[222,173]},
 'empty outer dereferences ignored argument':m=>m.profiles[0].cases[13].result={tag:'stuck',reason:'dangling memory reference'},
 'empty inner executes its postlude':m=>m.profiles[0].cases[14].result.bytes=[170,187],
 'empty inner fails to suppress dangling body':m=>m.profiles[0].cases[15].result={tag:'stuck',reason:'dangling memory reference'},
 'missing inner accepted':m=>m.profiles[0].cases[16].result={tag:'success',locals:[]},
 'missing outer accepted':m=>m.profiles[0].cases[17].result={tag:'success',locals:[]},
 'bad inner frame accepted':m=>m.profiles[0].cases[18].result={tag:'success',locals:[]},
 'bad outer frame accepted':m=>m.profiles[0].cases[19].result={tag:'success',locals:[]},
 'empty payload padded':m=>m.profiles[0].cases[20].result.bytes=[0],
 'inner panic shortened':m=>m.profiles[0].cases[21].result.bytes.pop(),
 'late11 body falsely completes':m=>m.profiles[0].cases[33].result={tag:'revert',bytes:[222,173]},
 'normal9 falsely completes':m=>m.profiles[0].cases[34].result={tag:'revert',bytes:[170,187]},
 'normal10 falsely times out':m=>m.profiles[0].cases[35].result={tag:'timeout'},
 'return10 falsely completes':m=>m.profiles[0].cases[36].result={tag:'revert',bytes:[170,187]},
 'return11 falsely times out':m=>m.profiles[0].cases[37].result={tag:'timeout'},
 'body dangling swallowed':m=>m.profiles[0].cases[38].result={tag:'revert',bytes:[]},
 'late frame restoration lost':m=>m.profiles[0].cases[33].after.frame.types=['bytes.memory','bytes.memory'],
 'saved frame bool cleared':m=>m.profiles[0].cases[0].after.frame.bool=false,
 'returned refs swapped':m=>m.profiles[0].cases[12].result.locals.reverse(),
 'ignored dangling ref reset':m=>m.profiles[0].cases[13].result.locals[0].logicalIndex=0,
 'wrong input local scope':m=>m.profiles[0].cases[0].inputLocals.pop(),
 'raw dirty bool cleaned':m=>m.profiles[0].cases[0].after.raw[0]='1',
 'raw dirty small reset':m=>m.profiles[0].cases[0].after.raw[3]='257',
 'same-type raw functions aliased':m=>m.profiles[0].cases[0].after.raw[4]=m.profiles[0].cases[0].after.raw[1],
 'old nonword alias changed':m=>m.profiles[0].cases[0].after.alias.bytes=[222,173],
 'heap payload changed with same error':m=>m.profiles[0].cases[0].after.object.bytes=[170,187],
 'heap extent changed':m=>m.profiles[0].cases[0].after.next=1,
 'outer EM scope not restored':m=>m.profiles[0].cases[0].outerRef.logicalIndex=1,
 'caller log prefix dropped':m=>m.profiles[0].cases[0].after.logs=[],
 'credit order reversed':m=>m.profiles[0].cases[0].after.events.reverse(),
 'credit value replaced':m=>m.profiles[0].cases[0].after.events[1].value='9',
 'physical high bytes lost':m=>m.profiles[0].cases[0].physicalAfter.word='2',
 'wrong owned owner':m=>m.profiles[0].cases[0].physicalAfter.ownedJournal[0][1]='2',
 'wrong residual slot':m=>m.profiles[0].cases[0].physicalAfter.residualJournal[0][2]='44',
 'wrong saved owned byte':m=>m.profiles[0].cases[0].physicalAfter.ownedJournal[0][4]=2,
 'residual journal lost':m=>m.profiles[0].cases[0].physicalAfter.residualJournal=[],
 'source journal count lost':m=>m.profiles[0].cases[0].physicalAfter.sourceJournalLength=0,
 'wrong source journal owner with equal error':m=>m.profiles[0].cases[0].physicalAfter.sourceJournal[0].address='2',
 'wrong old journal nonce':m=>m.profiles[0].cases[0].physicalAfter.sourceJournal[0].old.nonce=1,
 'wrong old c value':m=>m.profiles[0].cases[0].physicalAfter.sourceJournal[0].old.storage.cValue=true,
 'wrong current persistent state':m=>m.profiles[0].cases[0].physicalAfter.currentAccount.storage.cValue=false,
 'wrong current transient':m=>m.profiles[0].cases[0].physicalAfter.currentTransient.cValue=true,
 'invented native pass':m=>m.nativeComparisons=1,'invented full proof':m=>m.fullProofGate='pass',
 'missing before state':m=>delete m.profiles[0].cases[0].before,'extra unvalidated field':m=>m.profiles[0].cases[0].extra=true
};
for(const[name,change]of Object.entries(mutations))test(name,()=>{const m=clone(expectedNestedModifierModel());change(m);assert.throws(()=>validateNestedModifierModel(m));});
for(const target of ['Solidity/Yul/Composition/NestedModifierPhysical.lean','tests/yul-composition/NestedModifierDriver.lean','tests/yul-composition/nested-modifier-expectations.json','tests/yul-composition/nested-modifier-ledger.json'])test('stale '+target,()=>assert.throws(()=>verifyNestedModifierInputs(name=>{const bytes=readFileSync(join(ROOT,name));return name===target?Buffer.concat([bytes,Buffer.from(' drift')]):bytes;})));
test('missing selected registration',()=>assert.throws(()=>verifyNestedModifierInputs(name=>{if(name==='tests/yul-composition/ledger.json'){const l=JSON.parse(readFileSync(join(ROOT,name)));delete l.nestedModifierEvidence;return Buffer.from(JSON.stringify(l));}return readFileSync(join(ROOT,name));})));
const directory='/workspace/vy5-composition/nested-modifier-20261102/readback-v1';
const report=JSON.parse(readFileSync(join(directory,'report.json')));
test('all78 actual Source executions and exact receipt replay',()=>assert.deepEqual(validateNestedModifierReport(report,directory),{sourcePipelines:2,sourceCases:78,nativeComparisons:0,fullProofGate:'pending'}));
const badReports={
 'wrong command':r=>r.command[5]='-j2', 'wrong dependency':r=>r.dependency='/tmp/other', 'failed process':r=>r.exit=1,
 'stale source identity':r=>r.bindings['Solidity/Yul/Composition/NestedModifierPhysical.lean']='0'.repeat(64),
 'stale runner identity':r=>r.bindings['scripts/yul-composition/nested-modifier-source.mjs']='0'.repeat(64),
 'wrong stdout hash':r=>r.stdoutSha256='0'.repeat(64), 'wrong stderr hash':r=>r.stderrSha256='0'.repeat(64),
 'dropped actual case':r=>r.model.profiles[0].cases.pop(),
 'wrong actual bytes':r=>r.model.profiles[0].cases[0].result.bytes=[170,187],
 'false summary':r=>r.summary.sourceCases=77, 'invented proof':r=>r.summary.fullProofGate='pass',
 'extra unvalidated evidence':r=>r.extra=true, 'missing model':r=>delete r.model
};
for(const[name,change]of Object.entries(badReports))test('report '+name,()=>{const r=clone(report);change(r);assert.throws(()=>validateNestedModifierReport(r,directory));});
for(const target of ['execution.json','lean.stdout','lean.stderr','lean.exit'])test('missing actual '+target,()=>assert.throws(()=>validateNestedModifierReport(report,directory,path=>{if(path.endsWith('/'+target))throw Error('missing evidence');return readFileSync(path,'utf8');})));
for(const target of ['execution.json','lean.stdout','lean.stderr','lean.exit'])test('malformed actual '+target,()=>assert.throws(()=>validateNestedModifierReport(report,directory,path=>path.endsWith('/'+target)?'malformed':readFileSync(path,'utf8'))));

test('H3 decisions answered; VY1 producer inputs pending, never silently passed',()=>{const p=JSON.parse(readFileSync(join(ROOT,'tests/yul-composition/vy1-h3-input-obligations.json')));assert.equal(p.owner,'VY1');assert.equal(p.producerCommit,null);assert.equal(p.producerPackage,null);assert.equal(p.reask,false);assert.equal(p.duplicateOwnerImplementation,false);assert.deepEqual(p.gates[1].decision,{legacy:512,viaIR:0});assert.equal(p.status,'pending committed producer evidence; human decisions answered');assert.equal(JSON.parse(readFileSync(join(ROOT,'tests/yul-composition/ledger.json'))).vy1H3InputObligations,'tests/yul-composition/vy1-h3-input-obligations.json');});
