// Exact selected scalar-memory-ops observations, separate from full source admission.
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {replayBytecode} from '../../scripts/evm-reference/replay.mjs';
const sha=x=>createHash('sha256').update(x).digest('hex');
const word=x=>BigInt('0x'+x).toString();
// Independent actual object layout:1280pool plus96struct+128static array
// defaults AFTER the pool. Capturefree1632 before the36word observer allocation.
const W=2n**256n,A=2n**160n-1n,pad=BigInt('0x'+'a5'.repeat(32));
const left=x=>BigInt(x)<<232n;
const result=(mode=0)=>{
 const changed=mode===1||mode===2,n=mode===3?0:mode===5?1:2;
 const sv=changed?W-1n:W-128n,addr=changed?A:0x1234n,b3=left(changed?0xff00aa:0x112233);
 const a=changed?[W-1n,127n,W-128n,0n]:[W-128n,W-1n,0n,127n];
 const b=[left(changed?0xff00aa:0x112233),left(changed?0x010203:0xaa00ff)],c=changed?[A,0n]:[0x1234n,A];
 return [32,1152,sv,addr,b3,...a,n,...b,n,...c,3,left(0xeeddcc),1632,0,...Array(5).fill(pad),sv,addr,changed?255:17,a[0],a[3],n,n>0?(changed?255:17):0,n,n>0?c[0]:0,238,204,n,n>0?(changed?255:17):0,b[1]].map(String);
};
const vectors=[...['initial()','changed()','reversed()','shrinkZero()','regrow()','partialRegrow()'].map((signature,mode)=>({signature,args:[],failure:false,expected:result(mode)})),
 {signature:'revertOps()',args:[],failure:true,expected:[]},{signature:'initial()',args:[],failure:false,expected:result()}];
export function assertScalarMemoryOpsVariant(v){
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
export function assertScalarMemoryOpsReport(r){
 assert.equal(r.status,'working');assert.equal(r.variants.length,2);
 assert.deepEqual(r.variants.map(x=>x.viaIR),[false,true]);r.variants.forEach(assertScalarMemoryOpsVariant);
}
export async function replayScalarMemoryOps(compile){
 const source=readFileSync(new URL('./ScalarMemoryOps.sol',import.meta.url),'utf8');
 const variants=[];
 for(const viaIR of [false,true]){
  const input={language:'Solidity',sources:{'ScalarMemoryOps.sol':{content:source}},settings:{viaIR,evmVersion:'osaka',optimizer:{enabled:false,runs:200},metadata:{appendCBOR:false},
   outputSelection:{'*':{'*':['abi','evm.bytecode.object','evm.deployedBytecode.object','evm.methodIdentifiers','ir','irOptimized']}}}};
  const out=compile(input),errors=(out.errors??[]).filter(x=>x.severity==='error');
  if(errors.length){variants.push({viaIR,status:'blocked',errors});continue;}
  const a=out.contracts['ScalarMemoryOps.sol'].ScalarMemoryOps;
  const v={viaIR,inputSha256:sha(JSON.stringify(input)),sourceSha256:sha(source),creationSha256:sha(Buffer.from(a.evm.bytecode.object,'hex')),
   runtimeSha256:sha(Buffer.from(a.evm.deployedBytecode.object,'hex')),runtimeBytes:a.evm.deployedBytecode.object.length/2,ir:a.ir,irOptimized:a.irOptimized,vectors,...await replayBytecode(a,vectors)};
  if(v.status==='working')assertScalarMemoryOpsVariant(v);variants.push(v);
 }
 const r={kind:'external-reference-only',boundary:'Canonical scalar struct/fixed/dynamic/retained-array operations only; full Yul/source/compiler and dirty transport remain open. No universal writeback, Yul admission, allocation refinement or compiler/source correspondence theorem.',
  variants,status:variants.every(x=>x.status==='working')?'working':variants.some(x=>x.status==='broken')?'broken':'blocked'};
 if(r.status==='working')assertScalarMemoryOpsReport(r);return r;
}
