import {replayOwnedInventory} from './owned-inventory-reference.mjs';
import {replayJointMemory} from './joint-memory-reference.mjs';
// Lane-owned controls using the unchanged bounded reference-EVM helper.
// Kernel laws live in Solidity/Yul/Views; this is external evidence only.
import {readFileSync,writeFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {resolve} from 'node:path';
import {compiler} from '../../scripts/evm-reference/generated.mjs';
import {replayPhysicalFixtures} from './physical-upstream.mjs';
import {replayWriteback} from './writeback-reference.mjs';
import {replayResidual} from './residual-reference.mjs';
import {replayFinite} from './finite-reference.mjs';
import {replayHeapBytes} from './heap-bytes-reference.mjs';
import {replayScalarMemoryAlias} from './scalar-memory-alias-reference.mjs';
import {replayMemoryScalarWords} from './memory-scalar-words-reference.mjs';
import {replayScalarMemoryOps} from './scalar-memory-ops-reference.mjs';
import {replayRetainedMemberArrays} from './retained-member-arrays-reference.mjs';
import {replayMemberArrays} from './member-arrays-reference.mjs';
import {replayAggregateWriteback} from './aggregate-writeback-reference.mjs';
import {replayDynamicUint} from './dynamic-uint-reference.mjs';
import {replayWordWriteback} from './word-writeback-reference.mjs';
import {replayMixedHeap} from './mixed-heap-reference.mjs';
import {replayRetainedHeap} from './retained-heap-reference.mjs';
import {replayHeapResize} from './heap-resize-reference.mjs';
import {replayBytecode,INITIAL_GAS,STEP_LIMIT} from '../../scripts/evm-reference/replay.mjs';
const sha=b=>createHash('sha256').update(b).digest('hex');
const [compilerPath,outPath]=process.argv.slice(2);
if(!compilerPath||!outPath)throw Error('usage: node physical-reference.mjs PINNED_COMPILER REPORT');
const compile=compiler(compilerPath);
const source=readFileSync(new URL('./Physical.sol',import.meta.url),'utf8');
// Constants mirror the corresponding byte/word controls and fixed empty hash.
const expected=[['wordRoundtrip()', '0x12345678'],['lowByte()', '0xcd'],
 ['overlapRight()', '0x00010001020304050809'],['overlapLeft()', '0x02030405060706070809'],
 ['calldataTail()', '0'],['emptyHash()', '0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470'],
 ['residualSlots()', '49'], ['packedScalarFields()', '0x5566011234ff'],
 ['externalFunctionPacking()', '1']];
const vectors=expected.map(([signature,value])=>({signature,args:[],failure:false,expected:[BigInt(value).toString()]}));
// Dirty local/storage observations are external compiler evidence, not codec proofs.
vectors.push({signature:'dirtyLocal()',args:[],failure:false,expected:['1193046','86']},
 {signature:'dirtyBool()',args:[],failure:false,expected:['2','1']},
 {signature:'dirtyStorageBool()',args:[],failure:false,expected:['2','1']});
vectors.push({signature:'heterogeneousPacking()',args:[],failure:false,expected:[BigInt('0xa5a5a5a5a5a5a5a5a500000000000000000000000000000000001122331234ff').toString(),BigInt('0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a501fffffffffffffffffffffffffffffffe').toString()]},
 {signature:'fixedArrayPacking()',args:[],failure:false,expected:[BigInt('0xa5a500000a000009000008000007000006000005000004000003000002000001').toString(),BigInt('0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a500000c00000b').toString()]});
vectors.push({signature:'nestedFixedWords()',args:[],failure:false,expected:[BigInt('0xa5a500000a000009000008000007000006000005000004000003000002000001').toString(),BigInt('0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a500000c00000b').toString(),BigInt('0xa5a5a5a5a5a5a5a5a500000000000000000000000000000000001122331020ff').toString(),BigInt('0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a501fffffffffffffffffffffffffffffffe').toString(),BigInt('0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5').toString()]},
 {signature:'structArrayWords()',args:[],failure:false,expected:[BigInt('0xa5a5a5a5a5a5a5a5a500000000000000000000000000000000001122331020ff').toString(),BigInt('0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a501fffffffffffffffffffffffffffffffe').toString(),BigInt('0xa5a5a5a5a5a5a5a5a500000000000000000000000000000000001122341121fe').toString(),BigInt('0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a500fffffffffffffffffffffffffffffffd').toString(),BigInt('0xa5a5a5a5a5a5a5a5a500000000000000000000000000000000001122351222fd').toString(),BigInt('0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a501fffffffffffffffffffffffffffffffc').toString(),BigInt('0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5').toString()]});
const reports=[];
for(const viaIR of [false,true]){
 const input={language:'Solidity',sources:{'Physical.sol':{content:source}},settings:{viaIR,
  evmVersion:'osaka',optimizer:{enabled:false,runs:200},metadata:{appendCBOR:false},
  outputSelection:{'*':{'*':['abi','evm.bytecode.object','evm.deployedBytecode.object','evm.methodIdentifiers']}}}};
 const compiled=compile(input);
 const errors=(compiled.errors??[]).filter(e=>e.severity==='error');
 if(errors.length){reports.push({viaIR,status:'blocked',errors});continue;}
 const artifact=compiled.contracts['Physical.sol'].Physical;
 reports.push({viaIR,inputSha256:sha(JSON.stringify(input)),creationSha256:sha(Buffer.from(artifact.evm.bytecode.object,'hex')),
  runtimeSha256:sha(Buffer.from(artifact.evm.deployedBytecode.object,'hex')),vectors,...await replayBytecode(artifact,vectors)});
}
const upstream=await replayPhysicalFixtures(compile);
const writeback=await replayWriteback(compile);
const residual=await replayResidual(compile);
const finite=await replayFinite(compile);
const heapBytes=await replayHeapBytes(compile);
const heapResize=await replayHeapResize(compile);
const retainedHeap=await replayRetainedHeap(compile);
const mixedHeap=await replayMixedHeap(compile);
const wordWriteback=await replayWordWriteback(compile);
const dynamicUint=await replayDynamicUint(compile);
const aggregateWriteback=await replayAggregateWriteback(compile);
const memberArrays=await replayMemberArrays(compile);
const retainedMemberArrays=await replayRetainedMemberArrays(compile);
const memoryScalarWords=await replayMemoryScalarWords(compile);
const scalarMemoryOps=await replayScalarMemoryOps(compile);
const ownedInventory=await replayOwnedInventory(compile);
const jointMemory=await replayJointMemory(compile);
const scalarMemoryAlias=await replayScalarMemoryAlias(compile);
const report={ownedInventory,jointMemory,scalarMemoryAlias,memoryScalarWords,scalarMemoryOps,retainedMemberArrays,memberArrays,aggregateWriteback,dynamicUint,wordWriteback,mixedHeap,retainedHeap,heapResize,heapBytes,finite,residual,writeback,upstream,kind:'external-reference-only',compilerSha256:sha(readFileSync(compilerPath)),
 sourceSha256:sha(source),lockSha256:sha(readFileSync(new URL('../../scripts/evm-reference/package-lock.json',import.meta.url))),
 fork:'osaka',initialGas:INITIAL_GAS.toString(),stepLimit:STEP_LIMIT,reports};
writeFileSync(resolve(outPath),JSON.stringify(report,null,2)+'\n');
console.log(reports.map(r=>`${r.viaIR?'viaIR':'legacy'}: ${r.status}`).join('\n'));
for(const f of upstream.results)console.log(f.path+': '+f.variants.map(v=>`${v.viaIR?'viaIR':'legacy'} ${v.status}`).join(', '));
console.log('writeback: '+writeback.variants.map(v=>`${v.viaIR?'viaIR':'legacy'} ${v.status}`).join(', '));
console.log('residual: '+residual.variants.map(v=>`${v.viaIR?'viaIR':'legacy'} ${v.status}`).join(', '));
console.log('finite: '+finite.variants.map(v=>`${v.viaIR?'viaIR':'legacy'} ${v.status}`).join(', '));
console.log('heapBytes: '+heapBytes.variants.map(v=>`${v.viaIR?'viaIR':'legacy'} ${v.status}`).join(', '));
console.log('heapResize: '+heapResize.variants.map(v=>`${v.viaIR?'viaIR':'legacy'} ${v.status}`).join(', '));
console.log('retainedHeap: '+retainedHeap.variants.map(v=>`${v.viaIR?'viaIR':'legacy'} ${v.status}`).join(', '));
console.log('mixedHeap: '+mixedHeap.variants.map(v=>`${v.viaIR?'viaIR':'legacy'} ${v.status}`).join(', '));
console.log('wordWriteback: '+wordWriteback.variants.map(v=>`${v.viaIR?'viaIR':'legacy'} ${v.status}`).join(', '));
console.log('dynamicUint: '+dynamicUint.variants.map(v=>`${v.viaIR?'viaIR':'legacy'} ${v.status}`).join(', '));
console.log('aggregateWriteback: '+aggregateWriteback.variants.map(v=>`${v.viaIR?'viaIR':'legacy'} ${v.status}`).join(', '));
console.log('memberArrays: '+memberArrays.variants.map(v=>`${v.viaIR?'viaIR':'legacy'} ${v.status}`).join(', '));
console.log('retainedMemberArrays: '+retainedMemberArrays.variants.map(v=>`${v.viaIR?'viaIR':'legacy'} ${v.status}`).join(', '));
console.log('memoryScalarWords: '+memoryScalarWords.variants.map(v=>`${v.viaIR?'viaIR':'legacy'} ${v.status}`).join(', '));
console.log('scalarMemoryOps: '+scalarMemoryOps.variants.map(v=>`${v.viaIR?'viaIR':'legacy'} ${v.status}`).join(', '));
console.log('scalarMemoryAlias: '+scalarMemoryAlias.variants.map(v=>`${v.viaIR?'viaIR':'legacy'} ${v.status}`).join(', '));
console.log('jointMemory: '+jointMemory.variants.map(v=>`${v.viaIR?'viaIR':'legacy'} ${v.status}`).join(', '));
console.log('ownedInventory: '+ownedInventory.variants.map(v=>`${v.viaIR?'viaIR':'legacy'} ${v.status}`).join(', '));
process.exitCode=ownedInventory.status==='working'&&jointMemory.status==='working'&&scalarMemoryAlias.status==='working'&&memoryScalarWords.status==='working'&&scalarMemoryOps.status==='working'&&retainedMemberArrays.status==='working'&&memberArrays.status==='working'&&aggregateWriteback.status==='working'&&dynamicUint.status==='working'&&wordWriteback.status==='working'&&mixedHeap.status==='working'&&retainedHeap.status==='working'&&heapResize.status==='working'&&heapBytes.status==='working'&&finite.status==='working'&&residual.status==='working'&&reports.every(r=>r.status==='working')&&upstream.status==='working'&&writeback.status==='working'?0:1;
