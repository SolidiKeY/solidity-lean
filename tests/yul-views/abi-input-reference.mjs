import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {createRequire} from 'node:module';
import {machine,observation,creationObservation,INITIAL_GAS,STEP_LIMIT} from '../../scripts/evm-reference/replay.mjs';
const {keccak_256}=await import(createRequire(new URL('../../scripts/evm-reference/replay.mjs',import.meta.url)).resolve('@noble/hashes/sha3.js'));
const hex=x=>Buffer.from(x).toString('hex'),sha=x=>createHash('sha256').update(x).digest('hex');
const abi=xs=>'0x'+xs.map(x=>BigInt(x).toString(16).padStart(64,'0')).join('');
const reason=s=>'0x08c379a0'+abi([32,s.length]).slice(2)+Buffer.from(s).toString('hex').padEnd(64,'0');
const panic=n=>'0x4e487b71'+BigInt(n).toString(16).padStart(64,'0');
const max=(1n<<256n)-1n;
const valid=abi([32,3,7,max,77]),empty=abi([32,0]),unaligned=abi([33])+'a5'+abi([3,7,max,77]).slice(2),large=abi([32,1n<<64n]),short=abi([32,3,7,max]),dirty=abi([32,1,2]);
const result=(tag=0,n=3)=>abi([tag,n,n?(tag===1?99:7):0,n>1?max:0,n>2?77:0,n,n?(tag===1?99:7):0,n>1?max:0,n>2?77:0,1]);
const spec=[
 ['marker()',null,abi([4242])],['inspect(bytes)',valid,result()],['mutated(bytes)',valid,result(1)],['inspect(bytes)',empty,result(0,0)],
 ['inspect(bytes)',unaligned,result()],['at(bytes,uint256)',valid,abi([max]),false,1],['at(bytes,uint256)',valid,panic(50),true,3],
 ['inspect(bytes)','0x','0x',true],['inspect(bytes)',large,panic(65),true],['inspect(bytes)',short,'0x',true],['bools(bytes)',dirty,'0x',true],
 ['fail(bytes)',valid,reason('abi-array'),true],['marker()',null,abi([4242])],
 ['staticProbe(bytes)',valid,abi([1,64,320])+result().slice(2)],['staticProbe(bytes)',short,abi([0,64,0])],['inspect(bytes)',valid,result()],['marker()',null,abi([4242])]
];
const wordValues=x=>x.slice(2).match(/.{64}/g)?.map(x=>BigInt('0x'+x).toString())??[];
export const vectors=spec.map(([signature,packet,returnData,failure=false,index=null])=>({signature,packet,index,failure,returnData,expected:failure?[]:wordValues(returnData),storage:['4242']}));
const signatures=['marker()','inspect(bytes)','mutated(bytes)','at(bytes,uint256)','bools(bytes)','fail(bytes)','staticProbe(bytes)'];
const selectors=Object.fromEntries(signatures.map(s=>[s,hex(keccak_256(Buffer.from(s))).slice(0,8)]));
const encode=x=>{if(x.packet===null)return '0x'+selectors[x.signature];const raw=x.packet.slice(2),size=raw.length/2,padded=raw.padEnd(Math.ceil(size/32)*64,'0');return '0x'+selectors[x.signature]+abi(x.index===null?[32,size]:[64,x.index,size]).slice(2)+padded;};
export function assertAbiInputVariant(v){
 assert.equal(v.status,'working');assert.equal(v.initialGas,'100000000');assert.equal(v.stepLimit,5000000);
 for(const k of ['inputSha256','sourceSha256','creationSha256','runtimeSha256'])assert.match(v[k],/^[0-9a-f]{64}$/);
 assert.equal(v.sourceSha256,sha(readFileSync(new URL('./AbiInputAllocation.sol',import.meta.url))));
 assert.ok(Number.isSafeInteger(v.runtimeCodeBytes)&&v.runtimeCodeBytes>0);assert.deepEqual(v.methodIdentifiers,selectors);assert.deepEqual(v.vectors,vectors);assert.deepEqual(v.encodedCalls,vectors.map(encode));
 assert.deepEqual(v.storageLayout.storage.map(x=>[x.label,x.slot,x.offset]),[['marker','0',0]]);assert.deepEqual(v.transientStorageLayout.storage,[]);
 assert.equal(v.deployment.failed,false);assert.equal(v.deployment.exception,null);assert.equal(v.deployment.returnData,'0x');assert.equal(v.deployment.runtimeCodeSha256,v.runtimeSha256);assert.equal(v.deployment.runtimeCodeBytes,v.runtimeCodeBytes);
 assert.ok(v.deployment.steps>0&&v.deployment.steps<=STEP_LIMIT);assert.ok(BigInt(v.deployment.gasUsed)>=0n&&BigInt(v.deployment.gasUsed)<=INITIAL_GAS);
 assert.equal(v.observed.length,vectors.length);
 for(let i=0;i<vectors.length;i++){const x=vectors[i],z=v.observed[i];assert.equal(z.signature,x.signature);assert.equal(z.calldata,v.encodedCalls[i]);assert.equal(z.failed,x.failure);assert.equal(z.exception,x.failure?'revert':null);assert.deepEqual(z.values,x.expected);assert.equal(z.returnData,x.returnData);assert.deepEqual(z.storage,x.storage);assert.deepEqual(z.logs,[]);assert.ok(z.steps>0&&z.steps<=STEP_LIMIT);assert.ok(Number.isSafeInteger(z.maxStack)&&z.maxStack>=0&&z.maxStack<=1024);assert.ok(BigInt(z.gasUsed)>=0n&&BigInt(z.gasUsed)<=INITIAL_GAS);}
}
export function assertAbiInputReport(r){assert.equal(r.status,'working');assert.deepEqual(r.variants.map(v=>v.viaIR),[false,true]);r.variants.forEach(assertAbiInputVariant);}
export async function replayAbiInput(compile,onVariant=()=>{}){
 const source=readFileSync(new URL('./AbiInputAllocation.sol',import.meta.url),'utf8'),variants=[];
 for(const viaIR of [false,true]){
  const input={language:'Solidity',sources:{'AbiInputAllocation.sol':{content:source}},settings:{viaIR,evmVersion:'osaka',optimizer:{enabled:false,runs:200},metadata:{appendCBOR:false},outputSelection:{'*':{'':['ast'],'*':['abi','evm.bytecode.object','evm.deployedBytecode.object','evm.methodIdentifiers','storageLayout','transientStorageLayout','ir','irOptimized']}}}};
  const output=compile(input),errors=(output.errors??[]).filter(x=>x.severity==='error');if(errors.length){variants.push({viaIR,status:'blocked',errors});onVariant(variants.at(-1));continue;}
  const artifact=output.contracts['AbiInputAllocation.sol'].AbiInputAllocation,vm=await machine(STEP_LIMIT),observed=[];
  const made=await vm.call({data:Uint8Array.from(Buffer.from(artifact.evm.bytecode.object,'hex'))}),deployment=creationObservation(made.result.execResult,'constructor',made.metrics);assert.ok(made.result.createdAddress);
  for(const x of vectors){const calldata=encode(x),receipt=await vm.call({to:made.result.createdAddress,data:Uint8Array.from(Buffer.from(calldata.slice(2),'hex'))});const stored=await vm.evm.stateManager.getStorage(made.result.createdAddress,Buffer.alloc(32));observed.push({...observation(receipt.result.execResult,x.signature,receipt.metrics),calldata,storage:[stored.length?BigInt('0x'+hex(stored)).toString():'0'],logs:(receipt.result.execResult.logs??[]).map(([a,t,b])=>[hex(a),t.map(hex),hex(b)])});}
  const v={viaIR,status:'working',inputSha256:sha(JSON.stringify(input)),sourceSha256:sha(source),creationSha256:sha(Buffer.from(artifact.evm.bytecode.object,'hex')),runtimeSha256:sha(Buffer.from(artifact.evm.deployedBytecode.object,'hex')),runtimeCodeBytes:artifact.evm.deployedBytecode.object.length/2,storageLayout:artifact.storageLayout,transientStorageLayout:artifact.transientStorageLayout,methodIdentifiers:artifact.evm.methodIdentifiers,encodedCalls:vectors.map(encode),initialGas:INITIAL_GAS.toString(),stepLimit:STEP_LIMIT,vectors,deployment,observed,ir:artifact.ir,irOptimized:artifact.irOptimized};onVariant(v);assertAbiInputVariant(v);variants.push(v);
 }
 const r={status:variants.every(v=>v.status==='working')?'working':'blocked',kind:'external-reference-only',boundary:'Finite actual ABI memory uint256-array header/payload/MAX/unaligned offsets/aliases/empty/error/static decoding observations. No admission, lazy-calldata repair, seeded kernel equality, allocation profile or source/compiler adequacy.',variants};if(r.status==='working')assertAbiInputReport(r);return r;
}
