// Narrow selected byte/string fixture using the unchanged public bounded EVM.
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {replayBytecode} from '../../scripts/evm-reference/replay.mjs';
const sha=x=>createHash('sha256').update(x).digest('hex');
const word=x=>BigInt('0x'+x).toString();
const pad='a5'.repeat(32),aOld='112233'+'a5'.repeat(29),aNew='998877'+'a5'.repeat(29);
const bOld='61'.repeat(32),bNew='ff'+'62'.repeat(31),c='eeddcc'+'a5'.repeat(29);
// ABI bytes envelope plus16 exact memory/source observations. Entry free pointer
// is solc's0x80; objects advance it by384, boundaries by256. Never normalize it.
const result=(a,b,length=3)=>['32','512',String(length),word(a==='new'?aNew:aOld),'33',word(b==='new'?bNew:bOld),
 word((b==='new'?'62':'61')+'a5'.repeat(31)),'3',word(c),'512','0',word(pad),word(pad),word(pad),
 a==='new'?'153':'17',a==='new'?'153':'17','1','1'];
const boundaries=['32','512','0','31','32','33',word('ff'.repeat(31)+'a5'),word('ff'.repeat(32)),word('ff'.repeat(32)),
 word('ff'+'a5'.repeat(31)),'160','224','288','384','0','165','255','165'];
const vectors=[
 {signature:'unchanged()',args:[],failure:false,expected:result('old','old')},
 {signature:'byteChanged()',args:[],failure:false,expected:result('new','old')},
 {signature:'stringChanged()',args:[],failure:false,expected:result('old','new')},
 {signature:'twoForward()',args:[],failure:false,expected:result('new','new')},
 {signature:'twoReverse()',args:[],failure:false,expected:result('new','new')},
 {signature:'sameWrite()',args:[],failure:false,expected:result('old','old')},
 {signature:'headerChange()',args:[],failure:false,expected:result('old','old',4)},
 {signature:'boundaries()',args:[],failure:false,expected:boundaries},
 {signature:'explicitRevert()',args:[],failure:true,expected:[]},
 {signature:'unchanged()',args:[],failure:false,expected:result('old','old')},
];
export function assertHeapBytesVariant(v){
 assert.equal(v.status,'working');
 for(const name of ['inputSha256','sourceSha256','creationSha256','runtimeSha256'])assert.match(v[name],/^[a-f0-9]{64}$/);
 assert.equal(v.deployment?.failed,false);
 assert.equal(v.deployment.exception,null);assert.equal(v.deployment.returnData,'0x');
 assert.equal(v.deployment.runtimeCodeSha256,v.runtimeSha256);
 assert.ok(Number.isSafeInteger(v.runtimeBytes)&&v.runtimeBytes>0);assert.equal(v.deployment.runtimeCodeBytes,v.runtimeBytes);
 assert.deepEqual(v.vectors,vectors);assert.equal(v.observed.length,vectors.length);
 for(let i=0;i<vectors.length;i++){
  const e=vectors[i],a=v.observed[i];assert.equal(a.signature,e.signature);assert.equal(a.failed,e.failure);
  assert.equal(a.exception,e.failure?'revert':null);assert.deepEqual(a.values,e.expected);
  assert.equal(a.returnData,e.failure?'0x':'0x'+e.expected.map(x=>BigInt(x).toString(16).padStart(64,'0')).join(''));
 }
}
export function assertHeapBytesReport(r){
 assert.equal(r.status,'working');assert.equal(r.variants.length,2);
 assert.deepEqual(r.variants.map(x=>x.viaIR),[false,true]);r.variants.forEach(assertHeapBytesVariant);
}
export async function replayHeapBytes(compile){
 const source=readFileSync(new URL('./HeapBytes.sol',import.meta.url),'utf8'),variants=[];
 for(const viaIR of [false,true]){
  const input={language:'Solidity',sources:{'HeapBytes.sol':{content:source}},settings:{viaIR,evmVersion:'osaka',optimizer:{enabled:false,runs:200},metadata:{appendCBOR:false},
   outputSelection:{'*':{'*':['abi','evm.bytecode.object','evm.deployedBytecode.object','evm.methodIdentifiers','ir','irOptimized']}}}};
  const out=compile(input),errors=(out.errors??[]).filter(x=>x.severity==='error');
  if(errors.length){variants.push({viaIR,status:'blocked',errors});continue;}
  const a=out.contracts['HeapBytes.sol'].HeapBytes;
  const v={viaIR,inputSha256:sha(JSON.stringify(input)),sourceSha256:sha(source),creationSha256:sha(Buffer.from(a.evm.bytecode.object,'hex')),
   runtimeSha256:sha(Buffer.from(a.evm.deployedBytecode.object,'hex')),runtimeBytes:a.evm.deployedBytecode.object.length/2,ir:a.ir,irOptimized:a.irOptimized,vectors,...await replayBytecode(a,vectors)};
  if(v.status==='working')assertHeapBytesVariant(v);variants.push(v);
 }
 const r={kind:'external-reference-only',boundary:'Selected ordinary objects; fixed-shape logical preparation is not all Yul/heap semantics. Raw headerChange succeeds externally and remains open in the selected same-length writeback. No compiler correspondence or allocation refinement claim.',
  variants,status:variants.every(x=>x.status==='working')?'working':variants.some(x=>x.status==='broken')?'broken':'blocked'};
 if(r.status==='working')assertHeapBytesReport(r);return r;
}
