import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {validateReturningLedger,verifyReturning} from './returning-source.mjs';
const root=new URL('../../',import.meta.url);
const ledger=JSON.parse(readFileSync(new URL('tests/yul-composition/returning-ledger.json',root)));
const moduleText=readFileSync(new URL(ledger.module,root));
const provenance=JSON.parse(readFileSync(ledger.producerProvenance));
const read=name=>readFileSync('/workspace/vy5-dependencies-20261101/'+name);
const clone=x=>structuredClone(x);
test('registered concrete consumer and exact actual producer bodies',()=>assert.deepEqual(verifyReturning(),{kernelDeclarations:19,fullProofGate:'pending',freshNativeComparisons:0}));
const mutations={
 'missing signature':v=>v.facts.pop(),
 'reordered signatures':v=>v.facts.reverse(),
 'stale owned hash':v=>v.moduleSha256='0'.repeat(64),
 'wrong peer':v=>v.producer='0'.repeat(40),
 'claimed full coverage':v=>v.fullCoverage=true,
 'claimed full proof':v=>v.fullProofGate='pass',
 'dropped obligations':v=>v.originalObligations=23,
 'dropped combinations':v=>v.originalCombinations=5,
 'invented native evidence':v=>v.freshNativeComparisons=1,
 'erased journal failures':v=>v.existingNativeJournalFailures=0,
 'pretended revert producer':v=>v.pending=v.pending.filter(x=>x!=='ordinary nonempty revert producer packet'),
 'pretended try selector':v=>v.pending=v.pending.filter(x=>x!=='general Source try selector')
};
for(const [name,mutate]of Object.entries(mutations))test(name,()=>{const v=clone(ledger);mutate(v);assert.throws(()=>validateReturningLedger(v,moduleText,provenance,read));});
test('wrong source body despite unchanged report',()=>assert.throws(()=>validateReturningLedger(ledger,Buffer.concat([moduleText,Buffer.from(' drift')]),provenance,read)));
for(const kind of ['empty','missing','duplicate','wrong hash','wrong identity'])test('producer '+kind,()=>{
 const p=clone(provenance);
 if(kind==='empty')p.closure=[];
 if(kind==='missing')p.closure=p.closure.filter(x=>!x.path.endsWith('/GeneralReturning.lean'));
 if(kind==='duplicate')p.closure.push(p.closure[0]);
 if(kind==='wrong hash')p.closure[0].sha256='0'.repeat(64);
 if(kind==='wrong identity')p.producer='0'.repeat(40);
 assert.throws(()=>validateReturningLedger(ledger,moduleText,p,read));
});
test('actual private body must match committed producer digest',()=>assert.throws(()=>validateReturningLedger(ledger,moduleText,provenance,name=>Buffer.concat([read(name),Buffer.from(' drift')]))));

test('coordinated producer body and claimed hash tampering',()=>{
 const p=clone(provenance),path=p.closure[0].path;
 const changed=Buffer.concat([read(path),Buffer.from(' drift')]);
 p.closure[0].sha256=createHash('sha256').update(changed).digest('hex');
 assert.throws(()=>validateReturningLedger(ledger,moduleText,p,name=>name===path?changed:read(name)));
});
test('missing transitive producer body',()=>{
 const p=clone(provenance);p.closure=p.closure.filter(x=>!x.path.endsWith('/SourceBoundaryRules.lean'));
 assert.notEqual(p.closure.length,provenance.closure.length);
 assert.throws(()=>validateReturningLedger(ledger,moduleText,p,read));
});
test('redirected producer provenance path',()=>{
 const v=clone(ledger);v.producerProvenance='/tmp/alternative-provenance.json';
 assert.throws(()=>validateReturningLedger(v,moduleText,provenance,read));
});
