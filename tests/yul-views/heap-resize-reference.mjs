// Exact selected-footprint resize evidence, separate from full source admission.
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {replayBytecode} from '../../scripts/evm-reference/replay.mjs';
const sha=x=>createHash('sha256').update(x).digest('hex');
const word=x=>BigInt('0x'+x).toString();
const pad='a5'.repeat(32),a='112233'+'a5'.repeat(29),b='61'.repeat(32),tail='61'+'a5'.repeat(31),c='eeddcc'+'a5'.repeat(29);
// Complete20-word payload plus ABI bytes envelope. Pointer/free/zero observations
// stay exact, not normalized; allocation is the existing explicit384-byte pool.
const result=({alen=3,blen=33,bword=b,btail=tail,focusB=false}={})=>{
 const len=focusB?blen:alen,raw=focusB?bword:a;
 const first=len===0?0:parseInt(raw.slice(0,2),16);
 return ['32','640',String(alen),word(a),String(blen),word(bword),word(btail),'3',word(c),'512','0',word(pad),word(pad),word(pad),
  String(len),String(len),String(first),String(first),'1',word(raw),String(len),'34'];
};
const vectors=[
 {signature:'sameHeader()',args:[],failure:false,expected:result()},
 {signature:'grow3to4()',args:[],failure:false,expected:result({alen:4})},
 {signature:'shrink3to1()',args:[],failure:false,expected:result({alen:1})},
 {signature:'shrink3to0()',args:[],failure:false,expected:result({alen:0})},
 {signature:'grow3to32()',args:[],failure:false,expected:result({alen:32})},
 {signature:'string33to32()',args:[],failure:false,expected:result({blen:32,bword:'ff'+'62'.repeat(31),focusB:true})},
 {signature:'bucket31to32()',args:[],failure:false,expected:result({blen:32,bword:'11'.repeat(31)+'a5',btail:pad,focusB:true})},
 {signature:'shrink33to31()',args:[],failure:false,expected:result({blen:31,bword:'11'.repeat(32),btail:'11'+'a5'.repeat(31),focusB:true})},
 {signature:'grow33to64()',args:[],failure:false,expected:result({blen:64,focusB:true})},
 {signature:'beyondFootprint()',args:[],failure:false,expected:result({blen:65,focusB:true})},
 {signature:'explicitRevertResize()',args:[],failure:true,expected:[]},
 {signature:'sameHeader()',args:[],failure:false,expected:result()},
];
export function assertHeapResizeVariant(v){
 assert.equal(v.status,'working');
 for(const name of ['inputSha256','sourceSha256','parentSourceSha256','creationSha256','runtimeSha256'])assert.match(v[name],/^[a-f0-9]{64}$/);
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
export function assertHeapResizeReport(r){
 assert.equal(r.status,'working');assert.equal(r.variants.length,2);
 assert.deepEqual(r.variants.map(x=>x.viaIR),[false,true]);r.variants.forEach(assertHeapResizeVariant);
}
export async function replayHeapResize(compile){
 const source=readFileSync(new URL('./HeapResize.sol',import.meta.url),'utf8');
 const parent=readFileSync(new URL('./HeapBytes.sol',import.meta.url),'utf8'),variants=[];
 for(const viaIR of [false,true]){
  const input={language:'Solidity',sources:{'HeapResize.sol':{content:source},'HeapBytes.sol':{content:parent}},settings:{viaIR,evmVersion:'osaka',optimizer:{enabled:false,runs:200},metadata:{appendCBOR:false},
   outputSelection:{'*':{'*':['abi','evm.bytecode.object','evm.deployedBytecode.object','evm.methodIdentifiers','ir','irOptimized']}}}};
  const out=compile(input),errors=(out.errors??[]).filter(x=>x.severity==='error');
  if(errors.length){variants.push({viaIR,status:'blocked',errors});continue;}
  const a=out.contracts['HeapResize.sol'].HeapResize;
  const v={viaIR,inputSha256:sha(JSON.stringify(input)),sourceSha256:sha(source),parentSourceSha256:sha(parent),creationSha256:sha(Buffer.from(a.evm.bytecode.object,'hex')),
   runtimeSha256:sha(Buffer.from(a.evm.deployedBytecode.object,'hex')),runtimeBytes:a.evm.deployedBytecode.object.length/2,ir:a.ir,irOptimized:a.irOptimized,vectors,...await replayBytecode(a,vectors)};
  if(v.status==='working')assertHeapResizeVariant(v);variants.push(v);
 }
 const r={kind:'external-reference-only',boundary:'Separate selected-footprint implementation preserves fixed API. Beyond-original-footprint raw growth succeeds externally but remains OPEN; no exclusion/refusal or complete Y05/allocator/compiler proof.',
  variants,status:variants.every(x=>x.status==='working')?'working':variants.some(x=>x.status==='broken')?'broken':'blocked'};
 if(r.status==='working')assertHeapResizeReport(r);return r;
}
