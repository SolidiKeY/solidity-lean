import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {createRequire} from 'node:module';
const {keccak_256}=await import(createRequire(new URL('../../scripts/evm-reference/replay.mjs',import.meta.url)).resolve('@noble/hashes/sha3.js'));
import {machine,observation,creationObservation,INITIAL_GAS,STEP_LIMIT} from '../../scripts/evm-reference/replay.mjs';
const hex=x=>Buffer.from(x).toString('hex'),sha=x=>createHash('sha256').update(x).digest('hex');
const abi=xs=>'0x'+xs.map(x=>BigInt(x).toString(16).padStart(64,'0')).join('');
const address=0x1234567890123456789012345678901234567890n;
const prefix=(0xabn<<248n)|(address<<48n)|(0xaabbccn<<24n)|(0x1234n<<8n);
const words=b=>[b?1n:0n,prefix+BigInt(b),0x1234n,0xaabbccn<<232n,address,777n];
const reason=s=>'0x08c379a0'+(32n).toString(16).padStart(64,'0')+BigInt(s.length).toString(16).padStart(64,'0')+Buffer.from(s).toString('hex').padEnd(64,'0');
const spec=[['snap()',2],['writeThree()',3],['snap()',3],['childFail()',3,reason('owned bool')],['snap()',3],['write255()',255],['snap()',255],['staticProbe()',255,null,[0,0]],['snap()',255],['setFalse()',0],['snap()',0],['setTrue()',1],['snap()',1],['outerFail()',1,reason('outer')],['snap()',1],['writeThree()',3],['snap()',3]];
export const vectors=spec.map(([signature,b,error,custom])=>({signature,args:[],failure:!!error,returnData:error??abi(custom??words(b)),expected:error?[]:(custom??words(b)).map(String),storage:[String(prefix+BigInt(b)),'777']}));
const selectors=Object.fromEntries(['snap()','writeThree()','write255()','setFalse()','setTrue()','childFail()','outerFail()','staticProbe()'].map(s=>[s,hex(keccak_256(Buffer.from(s))).slice(0,8)]));
export function assertOwnedBoolVariant(v){
 assert.equal(v.status,'working');assert.equal(v.initialGas,'100000000');assert.equal(v.stepLimit,5000000);
 for(const k of ['inputSha256','sourceSha256','creationSha256','runtimeSha256'])assert.match(v[k],/^[0-9a-f]{64}$/);
 assert.equal(v.sourceSha256,sha(readFileSync(new URL('./OwnedBool.sol',import.meta.url))));
 assert.ok(Number.isSafeInteger(v.runtimeCodeBytes)&&v.runtimeCodeBytes>0);
 assert.deepEqual(v.methodIdentifiers,selectors);assert.deepEqual(v.vectors,vectors);assert.deepEqual(v.encodedCalls,vectors.map(x=>'0x'+selectors[x.signature]));
 assert.deepEqual(v.storageLayout.storage.map(x=>[x.label,x.slot,x.offset]),[['flag','0',0],['small','0',1],['data','0',3],['who','0',6],['marker','1',0]]);assert.deepEqual(v.transientStorageLayout.storage,[]);
 assert.equal(v.deployment.failed,false);assert.equal(v.deployment.exception,null);assert.equal(v.deployment.returnData,'0x');assert.equal(v.deployment.runtimeCodeSha256,v.runtimeSha256);assert.equal(v.deployment.runtimeCodeBytes,v.runtimeCodeBytes);
 assert.ok(v.deployment.steps>0&&v.deployment.steps<=STEP_LIMIT);assert.ok(BigInt(v.deployment.gasUsed)>=0n&&BigInt(v.deployment.gasUsed)<=INITIAL_GAS);
 assert.equal(v.observed.length,vectors.length);
 for(let i=0;i<vectors.length;i++){const a=v.observed[i],x=vectors[i];assert.equal(a.signature,x.signature);assert.equal(a.calldata,v.encodedCalls[i]);assert.equal(a.failed,x.failure);assert.equal(a.exception,x.failure?'revert':null);assert.deepEqual(a.values,x.expected);assert.equal(a.returnData,x.returnData);assert.deepEqual(a.storage,x.storage);assert.deepEqual(a.logs,[]);assert.ok(a.steps>0&&a.steps<=STEP_LIMIT);assert.ok(BigInt(a.gasUsed)>=0n&&BigInt(a.gasUsed)<=INITIAL_GAS);}
}
export function assertOwnedBoolReport(r){assert.equal(r.status,'working');assert.deepEqual(r.variants.map(x=>x.viaIR),[false,true]);r.variants.forEach(assertOwnedBoolVariant);}
export async function replayOwnedBool(compile,onVariant=()=>{}){
 const source=readFileSync(new URL('./OwnedBool.sol',import.meta.url),'utf8'),variants=[];
 for(const viaIR of [false,true]){
  const input={language:'Solidity',sources:{'OwnedBool.sol':{content:source}},settings:{viaIR,evmVersion:'osaka',optimizer:{enabled:false,runs:200},metadata:{appendCBOR:false},outputSelection:{'*':{'':['ast'],'*':['abi','evm.bytecode.object','evm.deployedBytecode.object','evm.methodIdentifiers','storageLayout','transientStorageLayout']}}}};
  const output=compile(input),errors=(output.errors??[]).filter(x=>x.severity==='error');if(errors.length){variants.push({viaIR,status:'blocked',errors});continue;}
  const a=output.contracts['OwnedBool.sol'].OwnedBool,vm=await machine(STEP_LIMIT),observed=[];
  const made=await vm.call({data:Uint8Array.from(Buffer.from(a.evm.bytecode.object,'hex'))}),deployment=creationObservation(made.result.execResult,'constructor',made.metrics);assert.ok(made.result.createdAddress);
  for(const x of vectors){const calldata='0x'+a.evm.methodIdentifiers[x.signature],receipt=await vm.call({to:made.result.createdAddress,data:Uint8Array.from(Buffer.from(calldata.slice(2),'hex'))});const storage=[];for(const slot of [0n,1n]){const b=await vm.evm.stateManager.getStorage(made.result.createdAddress,Buffer.from(slot.toString(16).padStart(64,'0'),'hex'));storage.push(b.length?BigInt('0x'+hex(b)).toString():'0');}observed.push({...observation(receipt.result.execResult,x.signature,receipt.metrics),calldata,storage,logs:(receipt.result.execResult.logs??[]).map(([a,t,b])=>[hex(a),t.map(hex),hex(b)])});}
  const v={viaIR,status:'working',inputSha256:sha(JSON.stringify(input)),sourceSha256:sha(source),creationSha256:sha(Buffer.from(a.evm.bytecode.object,'hex')),runtimeSha256:sha(Buffer.from(a.evm.deployedBytecode.object,'hex')),runtimeCodeBytes:a.evm.deployedBytecode.object.length/2,storageLayout:a.storageLayout,transientStorageLayout:a.transientStorageLayout,methodIdentifiers:a.evm.methodIdentifiers,encodedCalls:vectors.map(x=>'0x'+a.evm.methodIdentifiers[x.signature]),initialGas:INITIAL_GAS.toString(),stepLimit:STEP_LIMIT,vectors,deployment,observed};onVariant(v);assertOwnedBoolVariant(v);variants.push(v);
 }
 const r={status:variants.every(x=>x.status==='working')?'working':'blocked',kind:'external-reference-only',boundary:'Finite owned-byte truthiness, exact raw/padding, explicit literal assignment, static and frame rollback; not raw local cleanup/copy or whole source/compiler adequacy.',variants};if(r.status==='working')assertOwnedBoolReport(r);return r;
}
