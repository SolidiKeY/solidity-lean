// Exact selected memory-scalar-words observations, separate from full source admission.
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {replayBytecode} from '../../scripts/evm-reference/replay.mjs';
const sha=x=>createHash('sha256').update(x).digest('hex');
const word=x=>BigInt('0x'+x).toString();
// Canonical typed MEMORY stores: signed values sign extend to256bits;
// address/enum/uint are right-aligned; bytesN is LEFT-aligned, unlike storage.
const W=2n**256n;
const result=(mode=0)=>{
 const s8=mode===0?W-128n:mode===1?W-1n:mode===2?0n:127n;
 const s24=mode===0?W-2n**23n:mode===1?W-1n:mode===2?0n:2n**23n-1n;
 const u8=mode===0?255:mode===1?1:0,u24=mode===0?16777215:mode===1?65535:0,e=mode===0?2:0;
 return [s8,s24,u8,u24,BigInt('0x112233445566778899aabbccddeeff0011223344'),
 BigInt('0x112233')<<232n,BigInt('0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f')<<8n,e,
 BigInt('0x2233445566778899aabbccddeeff001122334455'),s8,s24,u8,u24,e,17,31].map(String);
};
const vectors=[...['bounds()','negativeOne()','zero()','maxima()'].map((signature,mode)=>({signature,args:[],failure:false,expected:result(mode)})),
 {signature:'revertWords()',args:[],failure:true,expected:[]},{signature:'bounds()',args:[],failure:false,expected:result()}];
export function assertMemoryScalarWordsVariant(v){
 assert.equal(v.status,'working');
 for(const name of ['inputSha256','sourceSha256','creationSha256','runtimeSha256'])assert.match(v[name],/^[a-f0-9]{64}$/);
 assert.equal(v.deployment?.failed,false);assert.equal(v.deployment.exception,null);assert.equal(v.deployment.returnData,'0x');
 assert.equal(v.deployment.runtimeCodeSha256,v.runtimeSha256);
 assert.ok(Number.isSafeInteger(v.runtimeBytes)&&v.runtimeBytes>0);assert.equal(v.deployment.runtimeCodeBytes,v.runtimeBytes);
 assert.deepEqual(v.vectors,vectors);assert.equal(v.observed.length,vectors.length);
 for(let i=0;i<vectors.length;i++){
  const e=vectors[i],a=v.observed[i];assert.equal(a.signature,e.signature);assert.equal(a.failed,e.failure);
  assert.equal(a.exception,e.failure?'revert':null);assert.deepEqual(a.values,e.expected);
  assert.equal(a.returnData,e.failure?'0x':'0x'+e.expected.map(x=>BigInt(x).toString(16).padStart(64,'0')).join(''));
 }
}
export function assertMemoryScalarWordsReport(r){
 assert.equal(r.status,'working');assert.equal(r.variants.length,2);
 assert.deepEqual(r.variants.map(x=>x.viaIR),[false,true]);r.variants.forEach(assertMemoryScalarWordsVariant);
}
export async function replayMemoryScalarWords(compile){
 const source=readFileSync(new URL('./MemoryScalarWords.sol',import.meta.url),'utf8');
 const variants=[];
 for(const viaIR of [false,true]){
  const input={language:'Solidity',sources:{'MemoryScalarWords.sol':{content:source}},settings:{viaIR,evmVersion:'osaka',optimizer:{enabled:false,runs:200},metadata:{appendCBOR:false},
   outputSelection:{'*':{'*':['abi','evm.bytecode.object','evm.deployedBytecode.object','evm.methodIdentifiers','ir','irOptimized']}}}};
  const out=compile(input),errors=(out.errors??[]).filter(x=>x.severity==='error');
  if(errors.length){variants.push({viaIR,status:'blocked',errors});continue;}
  const a=out.contracts['MemoryScalarWords.sol'].MemoryScalarWords;
  const v={viaIR,inputSha256:sha(JSON.stringify(input)),sourceSha256:sha(source),creationSha256:sha(Buffer.from(a.evm.bytecode.object,'hex')),
   runtimeSha256:sha(Buffer.from(a.evm.deployedBytecode.object,'hex')),runtimeBytes:a.evm.deployedBytecode.object.length/2,ir:a.ir,irOptimized:a.irOptimized,vectors,...await replayBytecode(a,vectors)};
  if(v.status==='working')assertMemoryScalarWordsVariant(v);variants.push(v);
 }
 const r={kind:'external-reference-only',boundary:'Canonical typed scalar MEMORY word audit only; dirty/noncanonical transport and full Yul/source correspondence remain open. No universal writeback, Yul admission, allocation refinement or compiler/source correspondence theorem.',
  variants,status:variants.every(x=>x.status==='working')?'working':variants.some(x=>x.status==='broken')?'broken':'blocked'};
 if(r.status==='working')assertMemoryScalarWordsReport(r);return r;
}
