// Exact selected aggregate-writeback observations, separate from full source admission.
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {replayBytecode} from '../../scripts/evm-reference/replay.mjs';
const sha=x=>createHash('sha256').update(x).digest('hex');
const word=x=>BigInt('0x'+x).toString();
const pad='a5'.repeat(32),text='ff61'+'a5'.repeat(30),other='eeddcc'+'a5'.repeat(29);
// Complete ABI bytes envelope and40-word payload. Explicit1536-byte pool starts
// before typed return defaults. Those uint[2]+Box defaults consume64+160 bytes
// after the pool; captured free pointer =128+1536+224=1888. Observation storage
// is allocated later. All pointers are checked as exact raw words.
const result=(changed=false,child=false)=>{
 const pointer=changed?'384':'128',first=child?'171':'255';
 return ['32','1280','3',word('112233'+'a5'.repeat(29)),'2',word((child?'ab':'ff')+'61'+'a5'.repeat(30)),'7','9',changed?'0':'1',changed?String(2n**256n-1n):'7',pointer,pointer,'1152','2','128','128','3',word(other),'1888','0',
  ...Array(6).fill(word(pad)),changed?'0':'1',changed?String(2n**256n-1n):'7',changed?'2':'3',changed?'2':'3',changed?first:'17',changed?first:'17','17','17','7','9','2','1','1',pointer,'51',first];
};
const vectors=[
 {signature:'initial()',args:[],failure:false,expected:result()},
 {signature:'allFields()',args:[],failure:false,expected:result(true)},
 {signature:'reverseFields()',args:[],failure:false,expected:result(true)},
 {signature:'updateSharedChild()',args:[],failure:false,expected:result(true,true)},
 {signature:'revertFields()',args:[],failure:true,expected:[]},
 {signature:'initial()',args:[],failure:false,expected:result()},
];
export function assertAggregateWritebackVariant(v){
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
export function assertAggregateWritebackReport(r){
 assert.equal(r.status,'working');assert.equal(r.variants.length,2);
 assert.deepEqual(r.variants.map(x=>x.viaIR),[false,true]);r.variants.forEach(assertAggregateWritebackVariant);
}
export async function replayAggregateWriteback(compile){
 const source=readFileSync(new URL('./AggregateWriteback.sol',import.meta.url),'utf8');
 const parent=readFileSync(new URL('./MixedHeap.sol',import.meta.url),'utf8'),variants=[];
 for(const viaIR of [false,true]){
  const input={language:'Solidity',sources:{'AggregateWriteback.sol':{content:source},'MixedHeap.sol':{content:parent}},settings:{viaIR,evmVersion:'osaka',optimizer:{enabled:false,runs:200},metadata:{appendCBOR:false},
   outputSelection:{'*':{'*':['abi','evm.bytecode.object','evm.deployedBytecode.object','evm.methodIdentifiers','ir','irOptimized']}}}};
  const out=compile(input),errors=(out.errors??[]).filter(x=>x.severity==='error');
  if(errors.length){variants.push({viaIR,status:'blocked',errors});continue;}
  const a=out.contracts['AggregateWriteback.sol'].AggregateWriteback;
  const v={viaIR,inputSha256:sha(JSON.stringify(input)),sourceSha256:sha(source),parentSourceSha256:sha(parent),creationSha256:sha(Buffer.from(a.evm.bytecode.object,'hex')),
   runtimeSha256:sha(Buffer.from(a.evm.deployedBytecode.object,'hex')),runtimeBytes:a.evm.deployedBytecode.object.length/2,ir:a.ir,irOptimized:a.irOptimized,vectors,...await replayBytecode(a,vectors)};
  if(v.status==='working')assertAggregateWritebackVariant(v);variants.push(v);
 }
 const r={kind:'external-reference-only',boundary:'Simultaneous canonical struct-member and real shared-child observations only. No universal writeback, Yul admission, allocation refinement or compiler/source correspondence theorem.',
  variants,status:variants.every(x=>x.status==='working')?'working':variants.some(x=>x.status==='broken')?'broken':'blocked'};
 if(r.status==='working')assertAggregateWritebackReport(r);return r;
}
