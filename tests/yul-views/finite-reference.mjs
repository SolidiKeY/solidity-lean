// Narrow owned finite-path fixture; uses the unchanged public bounded EVM.
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {replayBytecode} from '../../scripts/evm-reference/replay.mjs';
const sha=x=>createHash('sha256').update(x).digest('hex');
// Independent expectations: bool byte0, uint16 bytes1..2, uint256 next slot.
const raw=n=>(BigInt('0x'+'a5'.repeat(29)+'000000')+BigInt(n)).toString();
const other=BigInt('0x'+'a5'.repeat(31)+'37').toString();
const residual=BigInt('0x'+'a5'.repeat(32)).toString();
const values=(n,w,f,s,t='0')=>[raw(n),String(w),String(f),String(s),'55',other,residual,t];
const target=()=>values(0x123401,0x112233,1,0x1234);
const vectors=[
 {signature:'unchangedDefaults()',args:[],failure:false,expected:values(0,0,0,0)},
 {signature:'forwardChanges()',args:[],failure:false,expected:target()},
 {signature:'reverseChanges()',args:[],failure:false,expected:target()},
 {signature:'repeatedChanges()',args:[],failure:false,expected:target()},
 {signature:'dirtyOwned()',args:[],failure:false,expected:values(2,0,1,0)},
 {signature:'innerRevertPrefix()',args:[],failure:false,expected:values(1,0,1,0)},
 {signature:'outerRevertAfterChild()',args:[],failure:true,expected:[]},
 {signature:'readStored()',args:[],failure:false,expected:values(1,0,1,0)},
 {signature:'successAndTransient()',args:[],failure:false,expected:values(0x123401,0x112233,1,0x1234,'1')},
 {signature:'readStored()',args:[],failure:false,expected:target()},
];
function assertFiniteLayouts(storage,transient){
 assert.deepEqual(storage.storage.map(x=>[x.label,x.slot,x.offset]),[['flag','7',0],['small','7',1],['wide','8',0],['other','9',0]]);
 assert.deepEqual(storage.storage.map(x=>storage.types[x.type].numberOfBytes),['1','2','32','1']);
 assert.deepEqual(transient.storage.map(x=>[x.label,x.slot,x.offset]),[['txFlag','0',0]]);
 assert.deepEqual(transient.storage.map(x=>transient.types[x.type].numberOfBytes),['1']);
}
export function assertFiniteVariant(v){
 assertFiniteLayouts(v.storageLayout,v.transientStorageLayout);
 assert.equal(v.status,'working');assert.equal(v.deployment?.failed,false);
 assert.equal(v.deployment.exception,null);assert.equal(v.deployment.returnData,'0x');
 assert.equal(v.deployment.runtimeCodeSha256,v.runtimeSha256);
 assert.deepEqual(v.vectors,vectors);assert.equal(v.observed.length,vectors.length);
 for(let i=0;i<vectors.length;i++){
  const e=vectors[i],a=v.observed[i];
  assert.equal(a.signature,e.signature);assert.equal(a.failed,e.failure);
  assert.equal(a.exception,e.failure?'revert':null);assert.deepEqual(a.values,e.expected);
  assert.equal(a.returnData,e.failure?'0x':'0x'+e.expected.map(x=>BigInt(x).toString(16).padStart(64,'0')).join(''));
 }
}
export function assertFiniteReport(r){
 assert.equal(r.status,'working');assert.equal(r.variants.length,2);
 assert.deepEqual(r.variants.map(x=>x.viaIR),[false,true]);r.variants.forEach(assertFiniteVariant);
}
export async function replayFinite(compile){
 const source=readFileSync(new URL('./Finite.sol',import.meta.url),'utf8'),variants=[];
 for(const viaIR of [false,true]){
  const input={language:'Solidity',sources:{'Finite.sol':{content:source}},settings:{viaIR,evmVersion:'osaka',optimizer:{enabled:false,runs:200},metadata:{appendCBOR:false},
   outputSelection:{'*':{'*':['abi','evm.bytecode.object','evm.deployedBytecode.object','evm.methodIdentifiers','storageLayout','transientStorageLayout']}}}};
  const out=compile(input),errors=(out.errors??[]).filter(x=>x.severity==='error');
  if(errors.length){variants.push({viaIR,status:'blocked',errors});continue;}
  const a=out.contracts['Finite.sol'].Finite;
  assertFiniteLayouts(a.storageLayout,a.transientStorageLayout);
  const v={viaIR,inputSha256:sha(JSON.stringify(input)),sourceSha256:sha(source),creationSha256:sha(Buffer.from(a.evm.bytecode.object,'hex')),
   runtimeSha256:sha(Buffer.from(a.evm.deployedBytecode.object,'hex')),storageLayout:a.storageLayout,transientStorageLayout:a.transientStorageLayout,
   vectors,...await replayBytecode(a,vectors)};
  if(v.status==='working')assertFiniteVariant(v);variants.push(v);
 }
 const r={kind:'external-reference-only',boundary:'Finite canonical registration; dirty bool2 remains observable. Administrative none/default identity is kernel-only. No full ownership or Lean/EVM correspondence claim.',
  variants,status:variants.every(x=>x.status==='working')?'working':variants.some(x=>x.status==='broken')?'broken':'blocked'};
 if(r.status==='working')assertFiniteReport(r);return r;
}
