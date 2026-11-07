import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {join} from 'node:path';
import {ROOT,sha} from './harness.mjs';
import {verifyFailureInputs,validateFailureProvenance,expectedFailureModel,validateFailureModel,validateFailureReport} from './failure-source.mjs';
const clone=x=>structuredClone(x);
const directory='/workspace/vy5-composition/failure-consumer-20261102/readback-v1';
const report=JSON.parse(readFileSync(join(directory,'report.json')));
const provenance=JSON.parse(readFileSync('/workspace/vy5-composition/failure-consumer-20261102/producer-provenance.json'));
const readProducer=name=>readFileSync('/workspace/vy5-dependencies-20261101/'+name);
test('exact owned/private/runner/producer/source registration',()=>assert.equal(Object.keys(verifyFailureInputs()).length,6));
test('independently frozen selected Source failure model',()=>assert.deepEqual(validateFailureModel(expectedFailureModel()),{sourcePipelines:2,orderedSourceCases:30,copyWindowProfiles:2,nativeComparisons:0,fullProofGate:'pending'}));
test('all actual Source/copy/decode observations and full receipt',()=>assert.deepEqual(validateFailureReport(report,directory),{sourcePipelines:2,orderedSourceCases:30,copyWindowProfiles:2,nativeComparisons:0,fullProofGate:'pending'}));
const changes={
 'missing pipeline':m=>m.profiles.pop(), 'pipeline order':m=>m.profiles.reverse(),
 'missing case':m=>m.profiles[0].cases.pop(), 'case order':m=>m.profiles[0].cases.reverse(),
 'known producer wrong full selector':m=>m.profiles[0].cases[0].producer.status.bytes[0]^=1,
 'known producer wrong low payload byte':m=>m.profiles[0].cases[0].producer.status.bytes[35]=86,
 'consumer full selector lost':m=>m.profiles[0].cases[0].consumer.status.bytes=m.profiles[0].cases[0].consumer.status.bytes.slice(4),
 'consumer full high payload lost':m=>m.profiles[0].cases[0].consumer.status.bytes[4]=0,
 'consumer truncates byte35':m=>m.profiles[0].cases[0].consumer.status.bytes.pop(),
 'consumer suppresses revert':m=>m.profiles[0].cases[0].consumer.status={tag:'success',bytes:[]},
 'stale source identity hidden by control relabel':m=>m.profiles[0].cases[0].layer='decoder-boundary-control',
 'boundary control claimed real callee':m=>m.profiles[0].cases[9].layer='actual-known-call',
 'child revert fails balance rollback':m=>m.profiles[0].cases[0].producer.completion.state.world[2].account.balance='4',
 'child revert loses nonce prefix37':m=>m.profiles[0].cases[0].producer.completion.state.world[1].account.nonce=0,
 'child revert leaves transferred journal':m=>m.profiles[0].cases[0].producer.completion.state.journal.push(m.profiles[0].cases[0].producer.completion.state.journal[0]),
 'caller journal order wrong':m=>m.profiles[0].cases[0].consumer.state.journal.reverse(),
 'catch loses old local alias':m=>m.profiles[0].cases[0].consumer.state.locals.reverse(),
 'catch loses saved fnLocals':m=>m.profiles[0].cases[0].consumer.state.fnLocals=[],
 'catch loses input object':m=>m.profiles[0].cases[0].consumer.state.heap[0]=null,
 'catch allocates wrong36byte payload':m=>m.profiles[0].cases[0].consumer.state.heap[2].bytes[35]=86,
 'catch silently omits allocation':m=>m.profiles[0].cases[0].consumer.state.heapNext=2,
 'catch source storage touched':m=>m.profiles[0].cases[0].consumer.state.world[2].account.storagePresence[0]=true,
 'catch transient touched':m=>m.profiles[0].cases[0].consumer.state.world[2].transientPresence[0]=true,
 'retained error buffer staleOLD':m=>m.profiles[0].cases[0].producer.completion.returndata=[9,8,7,6],
 'ordered observation log/event swapped':m=>m.profiles[0].cases[0].producer.completion.trace.reverse(),
 'ordered topic lost':m=>m.profiles[0].cases[0].producer.completion.trace[3].topics.pop(),
 'wrong log emitter':m=>m.profiles[0].cases[0].producer.completion.trace[3].emitter='48',
 'wrong log bytes':m=>m.profiles[0].cases[0].producer.completion.trace[3].data[1]=0,
 'source legacy log discarded':m=>m.profiles[0].cases[0].consumer.state.legacyLogs=[],
 'source event prefix discarded':m=>m.profiles[0].cases[0].consumer.state.events=[],
 'raw bool cleaned':m=>m.profiles[0].cases[0].consumer.raw.bool='1',
 'raw uint8 cleaned':m=>m.profiles[0].cases[0].consumer.raw.uint8='1',
 'raw same-type function alias':m=>m.profiles[0].cases[0].consumer.raw.second=clone(m.profiles[0].cases[0].consumer.raw.first),
 'raw function selector truncated':m=>m.profiles[0].cases[0].consumer.raw.second.selector='4294967295',
 'raw nonword alias changed':m=>m.profiles[0].cases[0].consumer.raw.memory.logicalIndex=2,
 'wrong residual owner':m=>m.profiles[0].cases[0].producer.completion.journals.residual[0][1]='48',
 'wrong residual slot':m=>m.profiles[0].cases[0].producer.completion.journals.residual[0][2]='8',
 'lost residual high prefix':m=>m.profiles[0].cases[0].producer.completion.journals.residual[0][3]='0',
 'lost saved owned byte':m=>m.profiles[0].cases[0].producer.completion.journals.owned[0][4]=2,
 'wrong current owned dirty byte':m=>m.profiles[0].cases[0].producer.completion.journals.selectedOwnedByte=1,
 'consumer timeout erased new allocation':m=>m.profiles[0].cases[2].consumer.state.heap[2]=null,
 'consumer timeout called producer timeout':m=>m.profiles[0].cases[2].producer.completed=false,
 'entered timeout called completed revert':m=>m.profiles[0].cases[3].producer.completed=true,
 'entered timeout falsely rolls back transfer':m=>m.profiles[0].cases[3].consumer.state.world[2].account.balance='11',
 'entered timeout overwrites OLD return buffer':m=>m.profiles[0].cases[3].producer.completion.returndata=clone(m.profiles[0].cases[0].producer.completion.returndata),
 'entered timeout allocates catch object':m=>m.profiles[0].cases[3].consumer.state.heapNext=3,
 'empty refusal relabelled Denied':m=>m.profiles[0].cases[4].consumer.status.bytes=clone(m.profiles[0].cases[0].consumer.status.bytes),
 'overflow refusal mutates balance':m=>m.profiles[0].cases[5].consumer.state.world[4].account.balance='30',
 'adapter None converted empty result':m=>m.profiles[0].cases[6].producer={status:{tag:'revert',bytes:[]}},
 'static wrong kind accepted':m=>m.profiles[0].cases[7].consumer=clone(m.profiles[0].cases[1].consumer),
 'nonstatic invalid frame accepted':m=>m.profiles[0].cases[8].producer=clone(m.profiles[0].cases[1].producer),
 'wrong selector control silently cleaned':m=>m.profiles[0].cases[9].consumer.status.bytes[0]^=1,
 'wrong payload control silently cleaned':m=>m.profiles[0].cases[10].consumer.status.bytes[35]=85,
 'truncated error padded to36':m=>m.profiles[0].cases[11].consumer.status.bytes.push(85),
 'shortsuccess not decoded as emptyrevert':m=>m.profiles[0].cases[13].consumer.status={tag:'success',bytes:[]},
 'normal success always reverts':m=>m.profiles[0].cases[14].consumer.status={tag:'revert',bytes:[]},
 'copied wrong source offset':m=>m.profiles[0].copied.physicalBytes[1]=34,
 'copied wrong direction':m=>m.profiles[0].copied.physicalBytes[2]=17,
 'copied source heap not updated':m=>m.profiles[0].copied.state.heap[1].bytes=[161,178,195,212,229,246],
 'postcopy catch rethrows ONLY selected2bytes':m=>m.profiles[0].copiedCatch.status.bytes=[17,34],
 'postcopy catch loses copied heap':m=>m.profiles[0].copiedCatch.state.heap[1].bytes=[161,178,195,212,229,246],
 'postcopy loses full buffer':m=>m.profiles[0].copiedCatch.returndata=[17,34],
 'postcopy wrong journal':m=>m.profiles[0].copiedCatch.journals.owned=[],
 'invalidzero source37 accepted':m=>m.profiles[0].invalidCopy.copyIsNone=false,
 'invalidzero allocates':m=>m.profiles[0].invalidCopy.consumerIsNone=false,
 'invalidzero erases completedbuffer':m=>m.profiles[0].invalidCopy.completion.returndata=[],
 'exact endzero refused':m=>m.profiles[0].exactEnd=null,
 'known uint argument lowbyte wrong':m=>m.profiles[0].decodedKnownArgument='85',
 'fake new native comparison':m=>m.nativeComparisons=1,
 'fake full proof':m=>m.fullProofGate='pass',
 'missing actual before state':m=>delete m.profiles[0].cases[0].before,
 'extra unvalidated observation':m=>m.extra=true
};
for(const[name,change]of Object.entries(changes))test(name,()=>{const model=clone(expectedFailureModel());change(model);assert.throws(()=>validateFailureModel(model));});
for(const target of ['Solidity/Yul/Composition/FailurePhysical.lean','tests/yul-composition/FailureDriver.lean','tests/yul-composition/failure-expectations.json','tests/yul-composition/failure-ledger.json'])test('stale '+target,()=>assert.throws(()=>verifyFailureInputs(name=>{const bytes=readFileSync(join(ROOT,name));return name===target?Buffer.concat([bytes,Buffer.from(' drift')]):bytes;})));
test('missing new consumer registration',()=>assert.throws(()=>verifyFailureInputs(name=>{if(name==='tests/yul-composition/ledger.json'){const l=JSON.parse(readFileSync(join(ROOT,name)));delete l.failureEvidence;return Buffer.from(JSON.stringify(l));}return readFileSync(join(ROOT,name));})));
for(const kind of ['producer identity','missing closure','body drift','coordinated body and claimed hash'])test('producer '+kind,()=>{
 const p=clone(provenance);let reader=readProducer;
 if(kind==='producer identity')p.producer='0'.repeat(40);
 if(kind==='missing closure')p.closure=p.closure.filter(x=>!x.path.endsWith('/GeneralFailure.lean'));
 if(kind==='body drift')reader=name=>Buffer.concat([readProducer(name),Buffer.from(' drift')]);
 if(kind==='coordinated body and claimed hash'){const changed=Buffer.concat([readProducer(p.closure[0].path),Buffer.from(' drift')]);p.closure[0].sha256=sha(changed);reader=name=>name===p.closure[0].path?changed:readProducer(name);}
 assert.throws(()=>validateFailureProvenance(p,reader));
});
const reports={
 'wrong command':r=>r.command[5]='-j2','wrong dependency':r=>r.dependency='/tmp/other','failed source process':r=>r.exit=1,
 'wrong runnerSHA':r=>r.bindings['scripts/yul-composition/failure-source.mjs']='0'.repeat(64),
 'wrong sourceSHA':r=>r.bindings['Solidity/Yul/Composition/FailurePhysical.lean']='0'.repeat(64),
 'wrong producerSHA':r=>r.bindings['/workspace/vy5-composition/failure-consumer-20261102/producer-provenance.json']='0'.repeat(64),
 'wrong stdoutSHA':r=>r.stdoutSha256='0'.repeat(64),'wrong stderrSHA':r=>r.stderrSha256='0'.repeat(64),
 'missing observed case':r=>r.model.profiles[0].cases.pop(),'wrong actual bytes':r=>r.model.profiles[0].cases[0].consumer.status.bytes[35]=86,
 'false summary':r=>r.summary.orderedSourceCases=29,'fake proof':r=>r.summary.fullProofGate='pass',
 'extra unvalidated receipt':r=>r.extra=true,'missing model':r=>delete r.model
};
for(const[name,change]of Object.entries(reports))test('report '+name,()=>{const r=clone(report);change(r);assert.throws(()=>validateFailureReport(r,directory));});
for(const target of ['execution.json','lean.stdout','lean.stderr','lean.exit'])test('missing actual '+target,()=>assert.throws(()=>validateFailureReport(report,directory,path=>{if(path.endsWith('/'+target))throw Error('missing evidence');return readFileSync(path,'utf8');})));
for(const target of ['execution.json','lean.stdout','lean.stderr','lean.exit'])test('malformed actual '+target,()=>assert.throws(()=>validateFailureReport(report,directory,path=>path.endsWith('/'+target)?'malformed':readFileSync(path,'utf8'))));

test('full ordered topic vector cannot be reversed',()=>{const m=clone(expectedFailureModel());m.profiles[0].cases[0].producer.completion.trace[3].topics.reverse();assert.throws(()=>validateFailureModel(m));});
