// Exact selected dynamic-uint observations, separate from full source admission.
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {replayBytecode} from '../../scripts/evm-reference/replay.mjs';
const sha=x=>createHash('sha256').update(x).digest('hex');
const word=x=>BigInt('0x'+x).toString();
const pad=word('a5'.repeat(32)),max=String(2n**256n-1n),other=word('eeddcc'+'a5'.repeat(29));
// Pool128..1152 contains the two arrays, bytes and nested aliases. Dynamic local defaults
// use shared zero pointers and allocate no extra data.
// The observation buffer is allocated only AFTER oldFree is captured.
const result=(mode=0)=>{
 const n=mode===2?0:mode===3?1:3,changed=[1,5,6].includes(mode),both=[5,6].includes(mode);
 const a=changed?[max,'42','0']:['7','9',max],b=both?[max,'0']:['11','13'];
 return ['32','1024',String(n),...a,'2',...b,'3',other,'2','128','128','1152','0',String(n),String(n),String(n),
 n>0?a[0]:'0',n>1?a[1]:'0',n>2?a[2]:'0',...b,'238','204',pad,pad,pad,pad,'128','384','640','896'];
};
const vectors=[
 ...['initial()','changed()','shrinkZero()','regrowOne()','regrowAll()','firstThenSecond()','secondThenFirst()'].map((signature,mode)=>({signature,args:[],failure:false,expected:result(mode)})),
 {signature:'revertChanges()',args:[],failure:true,expected:[]},
 {signature:'initial()',args:[],failure:false,expected:result()},
];
export function assertDynamicUintVariant(v){
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
export function assertDynamicUintReport(r){
 assert.equal(r.status,'working');assert.equal(r.variants.length,2);
 assert.deepEqual(r.variants.map(x=>x.viaIR),[false,true]);r.variants.forEach(assertDynamicUintVariant);
}
export async function replayDynamicUint(compile){
 const source=readFileSync(new URL('./DynamicUint.sol',import.meta.url),'utf8');
 const variants=[];
 for(const viaIR of [false,true]){
  const input={language:'Solidity',sources:{'DynamicUint.sol':{content:source}},settings:{viaIR,evmVersion:'osaka',optimizer:{enabled:false,runs:200},metadata:{appendCBOR:false},
   outputSelection:{'*':{'*':['abi','evm.bytecode.object','evm.deployedBytecode.object','evm.methodIdentifiers','ir','irOptimized']}}}};
  const out=compile(input),errors=(out.errors??[]).filter(x=>x.severity==='error');
  if(errors.length){variants.push({viaIR,status:'blocked',errors});continue;}
  const a=out.contracts['DynamicUint.sol'].DynamicUint;
  const v={viaIR,inputSha256:sha(JSON.stringify(input)),sourceSha256:sha(source),creationSha256:sha(Buffer.from(a.evm.bytecode.object,'hex')),
   runtimeSha256:sha(Buffer.from(a.evm.deployedBytecode.object,'hex')),runtimeBytes:a.evm.deployedBytecode.object.length/2,ir:a.ir,irOptimized:a.irOptimized,vectors,...await replayBytecode(a,vectors)};
  if(v.status==='working')assertDynamicUintVariant(v);variants.push(v);
 }
 const r={kind:'external-reference-only',boundary:'Selected dynamic uint256 array, retained tail and nested alias observations only. No universal writeback, Yul admission, allocation refinement or compiler/source correspondence theorem.',
  variants,status:variants.every(x=>x.status==='working')?'working':variants.some(x=>x.status==='broken')?'broken':'blocked'};
 if(r.status==='working')assertDynamicUintReport(r);return r;
}
