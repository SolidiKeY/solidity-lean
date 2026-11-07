// Narrow owned companion-journal fixture; uses the unchanged public bounded EVM.
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {replayBytecode} from '../../scripts/evm-reference/replay.mjs';
const sha=x=>createHash('sha256').update(x).digest('hex');
const raw=tail=>BigInt('0x'+'a5'.repeat(30)+tail).toString();
const vectors=[
 {signature:'innerRevertPrefix()',args:[],failure:false,expected:[raw('0001'),'42','0','165','165']},
 {signature:'outerRevertAfterChild()',args:[],failure:true,expected:[]},
 {signature:'readStored()',args:[],failure:false,expected:[raw('0001'),'42','0','0','165']},
 {signature:'successAndTransient()',args:[],failure:false,expected:[raw('0101'),'43','1','7','165']},
 {signature:'readStored()',args:[],failure:false,expected:[raw('0101'),'43','0','0','165']},
];
export function assertResidualVariant(v){
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
export function assertResidualReport(r){
 assert.equal(r.status,'working');assert.equal(r.variants.length,2);
 assert.deepEqual(r.variants.map(x=>x.viaIR),[false,true]);r.variants.forEach(assertResidualVariant);
}
export async function replayResidual(compile){
 const source=readFileSync(new URL('./Residual.sol',import.meta.url),'utf8'),variants=[];
 for(const viaIR of [false,true]){
  const input={language:'Solidity',sources:{'Residual.sol':{content:source}},settings:{viaIR,evmVersion:'osaka',optimizer:{enabled:false,runs:200},metadata:{appendCBOR:false},
   outputSelection:{'*':{'*':['abi','evm.bytecode.object','evm.deployedBytecode.object','evm.methodIdentifiers','storageLayout','transientStorageLayout']}}}};
  const out=compile(input),errors=(out.errors??[]).filter(x=>x.severity==='error');
  if(errors.length){variants.push({viaIR,status:'blocked',errors});continue;}
  const a=out.contracts['Residual.sol'].Residual;
  assert.deepEqual(a.storageLayout.storage.map(x=>[x.label,x.slot,x.offset]),[['first','7',0],['second','7',1]]);
  assert.deepEqual(a.transientStorageLayout.storage.map(x=>[x.label,x.slot,x.offset]),[['txFlag','0',0]]);
  const v={viaIR,inputSha256:sha(JSON.stringify(input)),sourceSha256:sha(source),creationSha256:sha(Buffer.from(a.evm.bytecode.object,'hex')),
   runtimeSha256:sha(Buffer.from(a.evm.deployedBytecode.object,'hex')),storageLayout:a.storageLayout,transientStorageLayout:a.transientStorageLayout,
   vectors,...await replayBytecode(a,vectors)};
  if(v.status==='working')assertResidualVariant(v);variants.push(v);
 }
 const r={kind:'external-reference-only',boundary:'Fixed declared ownership; explicit within-transaction nonzero transient prefix. No ownership completeness or Lean/EVM correspondence claim.',
  variants,status:variants.every(x=>x.status==='working')?'working':variants.some(x=>x.status==='broken')?'broken':'blocked'};
 if(r.status==='working')assertResidualReport(r);return r;
}
