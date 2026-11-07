import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {resolve} from 'node:path';
import {createHash} from 'node:crypto';
import {validateIndexedWriteEvidence,validateScopedIndexedWriteAxioms,ROOT,THEOREMS,MODULE} from './indexed-write-kernel.mjs';
const report=JSON.parse(readFileSync('/workspace/vy5-composition/indexed-write-20261102/kernel-report.json'));
const sha=x=>createHash('sha256').update(x).digest('hex');
test('31 actual kernel signatures/axioms bind source and pending original ledger',()=>assert.deepEqual(validateIndexedWriteEvidence(report),{kernelComponent:'pass',facts:31,fullProofGate:'pending',nativeComparisons:0}));
for(const [name,change] of [
 ['missing proof',x=>x.theorems.pop()],['reordered proofs',x=>x.theorems.reverse()],['duplicate proof',x=>x.theorems[0]=x.theorems[1]],
 ['stale source',x=>x.moduleSha256='0'.repeat(64)],['wrong private body',x=>x.privateHead='0'.repeat(40)],
 ['false full pass',x=>x.fullProofGate='pass'],['false native comparison',x=>x.nativeComparisons=1],['fabricated finite cases',x=>x.finiteSourceCases=1],
 ['missing producer',x=>delete x.producerHashes[Object.keys(x.producerHashes)[0]]],['wrong producer',x=>x.producerHashes[Object.keys(x.producerHashes)[0]]='0'.repeat(64)],
 ['missing resource hash',x=>delete x.kernel.resourcesSha256],['stale raw receipt',x=>x.kernel.sha256='0'.repeat(64)]])
 test(name,()=>{const x=structuredClone(report);change(x);assert.throws(()=>validateIndexedWriteEvidence(x));});
for(const [name,change] of [['failed gate',x=>x.exit=1],['hidden stop',x=>x.stop='stopped'],['swap allowed',x=>x.memorySwap=x.memory+1],['relaxed headroom',x=>x.minimumAvailableBytes=1024]])
 test(name,()=>{const x=structuredClone(report),r=JSON.parse(readFileSync(x.kernel.resources));change(r);const bytes=Buffer.from(JSON.stringify(r));x.kernel.resourcesSha256=sha(bytes);assert.throws(()=>validateIndexedWriteEvidence(x,p=>p===x.kernel.resources?bytes:readFileSync(p)));});
for(const [name,change] of [['missing actual theorem',s=>s.replace("'Solidity.Yul.Composition.IndexedWritePhysical.outer_revert' depends on axioms:","'REMOVED' depends on axioms:")],['new axiom',s=>s.replace("'Solidity.Yul.Composition.IndexedWritePhysical.outer_revert' depends on axioms: [propext", "'Solidity.Yul.Composition.IndexedWritePhysical.outer_revert' depends on axioms: [sorryAx")],['absent KeySort',s=>s.replace('Build completed successfully (2 jobs).','REMOVED')],['wrong trust set',s=>s.replace('trust: 1330 sources','trust: 1 sources')]])
 test(name,()=>{const x=structuredClone(report),bytes=Buffer.from(change(String(readFileSync(x.kernel.log))));x.kernel.sha256=sha(bytes);assert.throws(()=>validateIndexedWriteEvidence(x,p=>p===x.kernel.log?bytes:readFileSync(p)));});
for(const [name,path,change] of [['missing registration','tests/yul-composition/ledger.json',x=>delete x.indexedWriteEvidence],['false original closure','tests/yul-composition/ledger.json',x=>x.obligations[0].status='done'],['missing signatures','tests/yul-composition/indexed-write-ledger.json',x=>x.theorems.pop()]])
 test(name,()=>assert.throws(()=>validateIndexedWriteEvidence(report,undefined,p=>{const b=readFileSync(resolve(ROOT,p));if(p!==path)return b;const x=JSON.parse(b);change(x);return Buffer.from(JSON.stringify(x));})));
test('same receipt cannot mask mutated actual source',()=>assert.throws(()=>validateIndexedWriteEvidence(report,undefined,p=>p===MODULE?Buffer.from(String(readFileSync(resolve(ROOT,p))).replace('0xab000002','0xab000001')):readFileSync(resolve(ROOT,p)))));
test('coordinated producer substitution rejected',()=>{const x=structuredClone(report);const keys=Object.keys(x.producerHashes);delete x.producerHashes[keys[0]];x.producerHashes[report.privateModule]=report.moduleSha256;assert.throws(()=>validateIndexedWriteEvidence(x));});
test('mutated private body cannot hide behind unchanged main source',()=>assert.throws(()=>validateIndexedWriteEvidence(report,p=>p===report.privateModule?Buffer.from('wrong private body'):readFileSync(p))));

for(const path of ['Solidity/Yul/Composition/PhysicalFrames.lean','Solidity/Yul/Views/OwnedBoolSource.lean','Solidity/Yul/World/ScalarEmitPort.lean'])
 test('transitive private drift rejected: '+path,()=>assert.throws(()=>validateIndexedWriteEvidence(report,p=>p==='/workspace/vy5-dependencies-20261101/'+path?Buffer.from('changed transitive body'):readFileSync(p))));
test('coordinated closure-manifest substitution rejected',()=>assert.throws(()=>validateIndexedWriteEvidence(report,undefined,p=>{const b=readFileSync(resolve(ROOT,p));if(p!=='tests/yul-composition/indexed-write-inputs.json')return b;const x=JSON.parse(b);delete x.dependencyClosure['Solidity/Yul/Views/OwnedBoolSource.lean'];return Buffer.from(JSON.stringify(x));})));
test('mutated canonical original producer provenance rejected',()=>assert.throws(()=>validateIndexedWriteEvidence(report,p=>p==='/workspace/vy5-composition/indexed-write-20261102/producer-provenance.json'?Buffer.from('{}'):readFileSync(p))));

test('actual scoped checker enumerates all31 declarations',()=>assert.equal(validateScopedIndexedWriteAxioms(String(readFileSync(report.kernel.log))).length,31));
test('scoped parser independently rejects a missing theorem',()=>{const log=String(readFileSync(report.kernel.log)).replace("'Solidity.Yul.Composition.IndexedWritePhysical.outer_revert' depends on axioms:","'REMOVED' depends on axioms:");assert.throws(()=>validateScopedIndexedWriteAxioms(log));});
test('scoped parser independently rejects a new axiom',()=>{const log=String(readFileSync(report.kernel.log)).replace("'Solidity.Yul.Composition.IndexedWritePhysical.outer_revert' depends on axioms: [propext", "'Solidity.Yul.Composition.IndexedWritePhysical.outer_revert' depends on axioms: [sorryAx");assert.throws(()=>validateScopedIndexedWriteAxioms(log));});
