// Exact selected member-arrays observations, separate from full source admission.
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {replayBytecode} from '../../scripts/evm-reference/replay.mjs';
const sha=x=>createHash('sha256').update(x).digest('hex');
const word=x=>BigInt('0x'+x).toString();
const pad=word('a5'.repeat(32)),aWord=word('112233'+'a5'.repeat(29)),otherWord=word('eeddcc'+'a5'.repeat(29));
// Explicit1792-byte pool128..1920 plus96+64static local defaults =2080.
// Capturefree before the56-word observation buffer. Independently specified
// ALL raw pointers/headers/words and logical aliases, payloads and gaps.
const result=(mode=0)=>{
 const changed=mode!==0,child=mode===3,flags=changed?['1','0','1']:['0','1','0'],ptr=changed?'1408':'1152',first=child?'171':'255';
 return ['32','1792',...flags,ptr,ptr,'3',...flags,'2',ptr,ptr,'3',aWord,'2',word((child?'ab':'ff')+'61'+'a5'.repeat(30)),'3',otherWord,'2080','0',
 ...flags,...flags,changed?'2':'3',changed?'2':'3',changed?first:'17',changed?first:'17',changed?'2':'3',changed?'2':'3',changed?first:'17',changed?first:'17','1','1',
 ...Array(7).fill(pad),ptr,ptr,ptr,ptr,'3','2','17',first,'238','51','97','204','0'];
};
const vectors=[
 {signature:'initial()',args:[],failure:false,expected:result()},
 {signature:'changed()',args:[],failure:false,expected:result(1)},
 {signature:'reversed()',args:[],failure:false,expected:result(2)},
 {signature:'sharedChild()',args:[],failure:false,expected:result(3)},
 {signature:'revertArrays()',args:[],failure:true,expected:[]},
 {signature:'initial()',args:[],failure:false,expected:result()},
];
export function assertMemberArraysVariant(v){
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
export function assertMemberArraysReport(r){
 assert.equal(r.status,'working');assert.equal(r.variants.length,2);
 assert.deepEqual(r.variants.map(x=>x.viaIR),[false,true]);r.variants.forEach(assertMemberArraysVariant);
}
export async function replayMemberArrays(compile){
 const source=readFileSync(new URL('./MemberArrays.sol',import.meta.url),'utf8');
 const variants=[];
 for(const viaIR of [false,true]){
  const input={language:'Solidity',sources:{'MemberArrays.sol':{content:source}},settings:{viaIR,evmVersion:'osaka',optimizer:{enabled:false,runs:200},metadata:{appendCBOR:false},
   outputSelection:{'*':{'*':['abi','evm.bytecode.object','evm.deployedBytecode.object','evm.methodIdentifiers','ir','irOptimized']}}}};
  const out=compile(input),errors=(out.errors??[]).filter(x=>x.severity==='error');
  if(errors.length){variants.push({viaIR,status:'blocked',errors});continue;}
  const a=out.contracts['MemberArrays.sol'].MemberArrays;
  const v={viaIR,inputSha256:sha(JSON.stringify(input)),sourceSha256:sha(source),creationSha256:sha(Buffer.from(a.evm.bytecode.object,'hex')),
   runtimeSha256:sha(Buffer.from(a.evm.deployedBytecode.object,'hex')),runtimeBytes:a.evm.deployedBytecode.object.length/2,ir:a.ir,irOptimized:a.irOptimized,vectors,...await replayBytecode(a,vectors)};
  if(v.status==='working')assertMemberArraysVariant(v);variants.push(v);
 }
 const r={kind:'external-reference-only',boundary:'Canonical fixed/header-preserving bool/reference arrays and real shared-child observations only. No universal writeback, Yul admission, allocation refinement or compiler/source correspondence theorem.',
  variants,status:variants.every(x=>x.status==='working')?'working':variants.some(x=>x.status==='broken')?'broken':'blocked'};
 if(r.status==='working')assertMemberArraysReport(r);return r;
}
