import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {createRequire} from 'node:module';
import {machine,observation,creationObservation,INITIAL_GAS,STEP_LIMIT} from '../../scripts/evm-reference/replay.mjs';
const {keccak_256}=await import(createRequire(new URL('../../scripts/evm-reference/replay.mjs',import.meta.url)).resolve('@noble/hashes/sha3.js'));
const hex=x=>Buffer.from(x).toString('hex'),sha=x=>createHash('sha256').update(x).digest('hex');
const abi=xs=>'0x'+xs.map(x=>BigInt(x).toString(16).padStart(64,'0')).join('');
const reason=s=>'0x08c379a0'+abi([32,s.length]).slice(2)+Buffer.from(s).toString('hex').padEnd(64,'0');
const panic='0x4e487b71'+(50n).toString(16).padStart(64,'0');
const N=h=>BigInt('0x'+h),pad=N('a5'.repeat(32));
const a=N('112233'+'a5'.repeat(29)),changed=N('998833'+'a5'.repeat(29)),b=N('61'.repeat(32)),bt=N('61'+'a5'.repeat(31)),c=N('eeddcc'+'a5'.repeat(29)),max=(1n<<256n)-1n;
const raw=(tag=0)=>{const changedOrder=tag===1||tag===2,number=tag===3?max:changedOrder?9:7;return abi([32,992,tag,4576,4736,2,4576,4576,1,number,4096,4096,4480,2,4096,4096,3,changedOrder?changed:a,33,b,bt,3,c,4832,0,pad,pad,pad,changedOrder?153:17,7,777,number,2]);};
const spec=[['marker()',abi([777])],['untouched()',raw()],['forward()',raw(1)],['reverse()',raw(2)],['maxed()',raw(3)],['panicAlias()',panic,true],['forward()',raw(1)],['fail()',reason('objects'),true],['marker()',abi([777])],['staticProbe()',abi([0,0,777])],['marker()',abi([777])],['untouched()',raw()],['forward()',raw(1)]];
const wordValues=x=>x.slice(2).match(/.{64}/g).map(x=>BigInt('0x'+x).toString());
export const vectors=spec.map(([signature,returnData,failure=false])=>({signature,args:[],failure,returnData,expected:failure?[]:wordValues(returnData),storage:['777']}));
const signatures=['marker()','untouched()','forward()','reverse()','maxed()','panicAlias()','fail()','staticProbe()','unchanged()','byteChanged()','stringChanged()','twoForward()','twoReverse()','sameWrite()','headerChange()','explicitRevert()','boundaries()'];
const selectors=Object.fromEntries(signatures.map(s=>[s,hex(keccak_256(Buffer.from(s))).slice(0,8)]));
export function assertObjectAllocationVariant(v){
 assert.equal(v.status,'working');assert.equal(v.initialGas,'100000000');assert.equal(v.stepLimit,5000000);
 for(const k of ['inputSha256','sourceSha256','parentSourceSha256','creationSha256','runtimeSha256'])assert.match(v[k],/^[0-9a-f]{64}$/);
 assert.equal(v.sourceSha256,sha(readFileSync(new URL('./ObjectAllocation.sol',import.meta.url))));
 assert.equal(v.parentSourceSha256,sha(readFileSync(new URL('./HeapBytes.sol',import.meta.url))));
 assert.ok(Number.isSafeInteger(v.runtimeCodeBytes)&&v.runtimeCodeBytes>0);
 assert.deepEqual(v.methodIdentifiers,selectors);assert.deepEqual(v.vectors,vectors);assert.deepEqual(v.encodedCalls,vectors.map(x=>'0x'+selectors[x.signature]));
 assert.deepEqual(v.storageLayout.storage.map(x=>[x.label,x.slot,x.offset]),[['marker','0',0]]);assert.deepEqual(v.transientStorageLayout.storage,[]);
 assert.equal(v.deployment.failed,false);assert.equal(v.deployment.exception,null);assert.equal(v.deployment.returnData,'0x');assert.equal(v.deployment.runtimeCodeSha256,v.runtimeSha256);assert.equal(v.deployment.runtimeCodeBytes,v.runtimeCodeBytes);
 assert.ok(v.deployment.steps>0&&v.deployment.steps<=STEP_LIMIT);assert.ok(BigInt(v.deployment.gasUsed)>=0n&&BigInt(v.deployment.gasUsed)<=INITIAL_GAS);
 assert.equal(v.observed.length,vectors.length);
 for(let i=0;i<vectors.length;i++){const x=vectors[i],z=v.observed[i];assert.equal(z.signature,x.signature);assert.equal(z.calldata,v.encodedCalls[i]);assert.equal(z.failed,x.failure);assert.equal(z.exception,x.failure?'revert':null);assert.deepEqual(z.values,x.expected);assert.equal(z.returnData,x.returnData);assert.deepEqual(z.storage,x.storage);assert.deepEqual(z.logs,[]);assert.ok(z.steps>0&&z.steps<=STEP_LIMIT);assert.ok(Number.isSafeInteger(z.maxStack)&&z.maxStack>=0&&z.maxStack<=1024);assert.ok(BigInt(z.gasUsed)>=0n&&BigInt(z.gasUsed)<=INITIAL_GAS);}
}
export function assertObjectAllocationReport(r){assert.equal(r.status,'working');assert.deepEqual(r.variants.map(v=>v.viaIR),[false,true]);r.variants.forEach(assertObjectAllocationVariant);}
export async function replayObjectAllocation(compile,onVariant=()=>{}){
 const source=readFileSync(new URL('./ObjectAllocation.sol',import.meta.url),'utf8'),parent=readFileSync(new URL('./HeapBytes.sol',import.meta.url),'utf8'),variants=[];
 for(const viaIR of [false,true]){
  const input={language:'Solidity',sources:{'ObjectAllocation.sol':{content:source},'HeapBytes.sol':{content:parent}},settings:{viaIR,evmVersion:'osaka',optimizer:{enabled:false,runs:200},metadata:{appendCBOR:false},outputSelection:{'*':{'':['ast'],'*':['abi','evm.bytecode.object','evm.deployedBytecode.object','evm.methodIdentifiers','storageLayout','transientStorageLayout','ir','irOptimized']}}}};
  const output=compile(input),errors=(output.errors??[]).filter(x=>x.severity==='error');if(errors.length){variants.push({viaIR,status:'blocked',errors});onVariant(variants.at(-1));continue;}
  const artifact=output.contracts['ObjectAllocation.sol'].ObjectAllocation,vm=await machine(STEP_LIMIT),observed=[];
  const made=await vm.call({data:Uint8Array.from(Buffer.from(artifact.evm.bytecode.object,'hex'))}),deployment=creationObservation(made.result.execResult,'constructor',made.metrics);assert.ok(made.result.createdAddress);
  for(const x of vectors){const calldata='0x'+artifact.evm.methodIdentifiers[x.signature],receipt=await vm.call({to:made.result.createdAddress,data:Uint8Array.from(Buffer.from(calldata.slice(2),'hex'))});const stored=await vm.evm.stateManager.getStorage(made.result.createdAddress,Buffer.alloc(32));observed.push({...observation(receipt.result.execResult,x.signature,receipt.metrics),calldata,storage:[stored.length?BigInt('0x'+hex(stored)).toString():'0'],logs:(receipt.result.execResult.logs??[]).map(([a,t,b])=>[hex(a),t.map(hex),hex(b)])});}
  const v={viaIR,status:'working',inputSha256:sha(JSON.stringify(input)),sourceSha256:sha(source),parentSourceSha256:sha(parent),creationSha256:sha(Buffer.from(artifact.evm.bytecode.object,'hex')),runtimeSha256:sha(Buffer.from(artifact.evm.deployedBytecode.object,'hex')),runtimeCodeBytes:artifact.evm.deployedBytecode.object.length/2,storageLayout:artifact.storageLayout,transientStorageLayout:artifact.transientStorageLayout,methodIdentifiers:artifact.evm.methodIdentifiers,encodedCalls:vectors.map(x=>'0x'+artifact.evm.methodIdentifiers[x.signature]),initialGas:INITIAL_GAS.toString(),stepLimit:STEP_LIMIT,vectors,deployment,observed,ir:artifact.ir,irOptimized:artifact.irOptimized};onVariant(v);assertObjectAllocationVariant(v);variants.push(v);
 }
 const r={status:variants.every(v=>v.status==='working')?'working':'blocked',kind:'external-reference-only',boundary:'Explicit finite ordinary struct/array allocations in a leased pool with two aliases, nested children, typed/raw full observations, two update orders, max word and exact failures. The4096lease/prelude guard is fixture-only, not a model cap. Not source admission, target allocation refinement or kernel/compiler correspondence.',variants};if(r.status==='working')assertObjectAllocationReport(r);return r;
}
