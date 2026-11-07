// Exact lane-owned fixture adapter: complete nonempty Panic data participates.
// Public bounded machine/observations reused; shared replayBytecode's empty-
// revert scalar profile remains unchanged. This is not a general host harness.
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {machine,observation,creationObservation,INITIAL_GAS,STEP_LIMIT} from '../../scripts/evm-reference/replay.mjs';
import {observeStorageWrites} from './physical-upstream.mjs';
const sha=x=>createHash('sha256').update(x).digest('hex');
const bytes=x=>Uint8Array.from(Buffer.from(x,'hex'));
const W=2n**256n,A=2n**160n-1n,L=x=>BigInt(x)<<232n;
const panic='0x4e487b71'+'0'.repeat(62)+'32';
const expected=[W-1n,1,L(0xff00aa),2,W-1n,42,W-1n,42,3,11,22,33,33,W-1n,42,1,0,3,L(0xaabbcc),1,255,W-1n,2,W-1n,0,0,2,2,204,42,42,W-1n].map(String);
const selectors={'joint(bool,bool)':'e5e79206','badAlias()':'b7310966','revertJoint()':'21832579'};
const calldataFor=e=>selectors[e.signature]+e.args.map(x=>BigInt(x).toString(16).padStart(64,'0')).join('');
const expectedFor=(reverse,regrow)=>{const x=[...expected];x[24]=regrow?'0':'777';x[25]=regrow?'0':'888';return [...x,String(reverse),String(regrow)];};
const vectors=[
 {signature:'joint(bool,bool)',args:['0','0'],failure:false,expected:expectedFor(0,0)},
 {signature:'joint(bool,bool)',args:['1','0'],failure:false,expected:expectedFor(1,0)},
 {signature:'joint(bool,bool)',args:['0','1'],failure:false,expected:expectedFor(0,1)},
 {signature:'joint(bool,bool)',args:['1','1'],failure:false,expected:expectedFor(1,1)},
 {signature:'badAlias()',args:[],failure:true,expected:[],revertData:panic},
 {signature:'revertJoint()',args:[],failure:true,expected:[],revertData:'0x'},
 {signature:'joint(bool,bool)',args:['0','0'],failure:false,expected:expectedFor(0,0)},
];
export function assertJointMemoryVariant(v){
 assert.equal(v.status,'working');assert.equal(v.initialGas,'100000000');assert.equal(v.stepLimit,5000000);
 for(const n of ['inputSha256','sourceSha256','creationSha256','runtimeSha256'])assert.match(v[n],/^[a-f0-9]{64}$/);
 assert.equal(v.deployment.failed,false);assert.equal(v.deployment.exception,null);assert.equal(v.deployment.returnData,'0x');
 assert.equal(v.deployment.runtimeCodeSha256,v.runtimeSha256);assert.equal(v.deployment.runtimeCodeBytes,v.runtimeBytes);assert.ok(Number.isSafeInteger(v.runtimeBytes)&&v.runtimeBytes>0);
 assert.equal(v.deployment.storageWriteCount,0);assert.deepEqual(v.storageWrites,[]);
 assert.deepEqual(v.vectors,vectors);assert.equal(v.observed.length,vectors.length);
 for(let i=0;i<vectors.length;i++){
  const e=vectors[i],a=v.observed[i];assert.equal(a.signature,e.signature);assert.equal(a.calldata,'0x'+calldataFor(e));assert.equal(a.failed,e.failure);assert.equal(a.exception,e.failure?'revert':null);
  assert.deepEqual(a.values,e.expected);assert.equal(a.storageWritesBefore,0);assert.equal(a.storageWritesAfter,0);
  assert.equal(a.returnData,e.failure?e.revertData:'0x'+e.expected.map(x=>BigInt(x).toString(16).padStart(64,'0')).join(''));
 }
}
export function assertJointMemoryReport(r){
 assert.equal(r.status,'working');assert.equal(r.variants.length,2);assert.deepEqual(r.variants.map(v=>v.viaIR),[false,true]);r.variants.forEach(assertJointMemoryVariant);
}
export async function replayJointMemory(compile){
 const source=readFileSync(new URL('./JointMemory.sol',import.meta.url),'utf8'),variants=[];
 for(const viaIR of [false,true]){
  const input={language:'Solidity',sources:{'JointMemory.sol':{content:source}},settings:{viaIR,evmVersion:'osaka',optimizer:{enabled:false,runs:200},metadata:{appendCBOR:false},
   outputSelection:{'*':{'*':['abi','evm.bytecode.object','evm.deployedBytecode.object','evm.methodIdentifiers','ir','irOptimized']}}}};
  const out=compile(input),errors=(out.errors??[]).filter(e=>e.severity==='error');if(errors.length){variants.push({viaIR,status:'blocked',errors});continue;}
  const a=out.contracts['JointMemory.sol'].JointMemory;
  const v={viaIR,inputSha256:sha(JSON.stringify(input)),sourceSha256:sha(source),creationSha256:sha(Buffer.from(a.evm.bytecode.object,'hex')),runtimeSha256:sha(Buffer.from(a.evm.deployedBytecode.object,'hex')),
   runtimeBytes:a.evm.deployedBytecode.object.length/2,ir:a.ir,irOptimized:a.irOptimized,vectors,initialGas:INITIAL_GAS.toString(),stepLimit:STEP_LIMIT,observed:[],storageWrites:[]};
  try{
   const vm=await machine();v.storageWrites=observeStorageWrites(vm);
   const created=await vm.call({data:bytes(a.evm.bytecode.object)});v.deployment=creationObservation(created.result.execResult,'constructor',created.metrics);v.deployment.storageWriteCount=v.storageWrites.length;
   assert.ok(created.result.createdAddress);assert.equal(v.deployment.runtimeCodeSha256,v.runtimeSha256);assert.equal(v.deployment.failed,false);assert.equal(v.storageWrites.length,0);
   for(const e of vectors){
    const selector=a.evm.methodIdentifiers[e.signature];assert.match(selector??'',/^[a-f0-9]{8}$/);
    assert.equal(selector,selectors[e.signature]);const calldata=calldataFor(e);
    const before=v.storageWrites.length,{result,metrics}=await vm.call({to:created.result.createdAddress,data:bytes(calldata)});
    const observed={...observation(result.execResult,e.signature,metrics),calldata:'0x'+calldata,storageWritesBefore:before,storageWritesAfter:v.storageWrites.length};v.observed.push(observed);
    assert.equal(observed.failed,e.failure);assert.equal(observed.exception,e.failure?'revert':null);assert.deepEqual(observed.values,e.expected);
    assert.equal(observed.returnData,e.failure?e.revertData:'0x'+e.expected.map(x=>BigInt(x).toString(16).padStart(64,'0')).join(''));assert.equal(v.storageWrites.length,0);
   }
   v.status='working';assertJointMemoryVariant(v);
  }catch(e){v.status=e.name==='AssertionError'?'broken':'blocked';v.reason=e.message;}
  variants.push(v);
 }
 const r={kind:'external-reference-only',boundary:'One exact joint struct/pointer/array retained alias fixture with complete Panic/index revert bytes and zero storage writes; not source/compiler adequacy or a general host adapter.',variants,
  status:variants.every(v=>v.status==='working')?'working':variants.some(v=>v.status==='broken')?'broken':'blocked'};
 if(r.status==='working')assertJointMemoryReport(r);return r;
}
