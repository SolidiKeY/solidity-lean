import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {createRequire} from 'node:module';
const {keccak_256}=await import(createRequire(new URL('../../scripts/evm-reference/replay.mjs',import.meta.url)).resolve('@noble/hashes/sha3.js'));
import {machine,observation,creationObservation,INITIAL_GAS,STEP_LIMIT} from '../../scripts/evm-reference/replay.mjs';
const hex=x=>Buffer.from(x).toString('hex'),sha=x=>createHash('sha256').update(x).digest('hex');
const abi=xs=>'0x'+xs.map(x=>BigInt(x).toString(16).padStart(64,'0')).join('');
const W=1n<<256n,P=1n<<248n;
const hash=n=>BigInt('0x'+hex(keccak_256(Buffer.from(BigInt(n).toString(16).padStart(64,'0'),'hex'))));
const H=hash(0);assert.ok(H>2n&&H+1n<W);
const A=0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee02010100n;
const B=0xabn*P+0x024dn,S=0xcdn*P+0x1234n;
const A1=A-(2n<<24n)+(3n<<24n),B1=B-(2n<<8n)+(255n<<8n);
const reason=s=>'0x08c379a0'+(32n).toString(16).padStart(64,'0')+BigInt(s.length).toString(16).padStart(64,'0')+Buffer.from(s).toString('hex').padEnd(64,'0');
const panic='0x4e487b71'+(50n).toString(16).padStart(64,'0');
function values(n,changed){return [n,n,n,n?33:0,n?1:0,n?1:0,changed?A1:A,changed?B1:B,0x1234n,S,777,999];}
const dynamic=xs=>abi([32,xs.length,...xs]);
const spec=[['snap()',0,0],['grow()',34,0],['snap()',34,0],['zero()',0,0],['snap()',0,0],['regrow()',34,0],['snap()',34,0],['payload()',34,1],['snap()',34,1],['childFail()',34,1,reason('dynamic bool')],['snap()',34,1],['outerFail()',34,1,reason('outer')],['snap()',34,1],['staticProbe()',34,1,null,[0,0]],['bounds()',34,1,panic],['snap()',34,1],['zero()',0,1],['regrow()',34,1],['snap()',34,1]];
const wordValues=h=>h.slice(2).match(/.{64}/g).map(x=>BigInt('0x'+x).toString());
export const vectors=spec.map(([signature,n,changed,error,custom])=>{const returnData=error??(custom?abi(custom):dynamic(values(n,changed)));return {signature,args:[],failure:!!error,returnData,expected:error?[]:wordValues(returnData),storage:[n,changed?A1:A,changed?B1:B,S,777].map(String)};});
const selectors=Object.fromEntries(['snap()','grow()','zero()','regrow()','payload()','childFail()','outerFail()','staticProbe()','bounds()'].map(s=>[s,hex(keccak_256(Buffer.from(s))).slice(0,8)]));
export function assertOwnedBoolDynamicVariant(v){
 assert.equal(v.status,'working');assert.equal(v.initialGas,'100000000');assert.equal(v.stepLimit,5000000);
 for(const k of ['inputSha256','sourceSha256','creationSha256','runtimeSha256'])assert.match(v[k],/^[0-9a-f]{64}$/);
 assert.equal(v.sourceSha256,sha(readFileSync(new URL('./OwnedBoolDynamic.sol',import.meta.url))));
 assert.ok(Number.isSafeInteger(v.runtimeCodeBytes)&&v.runtimeCodeBytes>0);
 assert.deepEqual(v.methodIdentifiers,selectors);assert.deepEqual(v.vectors,vectors);assert.deepEqual(v.encodedCalls,vectors.map(x=>'0x'+selectors[x.signature]));
 assert.deepEqual(v.storageLayout.storage.map(x=>[x.label,x.slot,x.offset]),[['xs','0',0],['small','1',0],['marker','2',0]]);assert.deepEqual(v.transientStorageLayout.storage,[]);assert.equal(v.dataRoot,H.toString());assert.equal(v.storageLayout.types[v.storageLayout.storage[0].type].encoding,'dynamic_array');assert.equal(v.storageLayout.types[v.storageLayout.types[v.storageLayout.storage[0].type].base].numberOfBytes,'1');assert.equal(v.storageLayout.types[v.storageLayout.types[v.storageLayout.storage[0].type].base].label,'bool');
 assert.equal(v.deployment.failed,false);assert.equal(v.deployment.exception,null);assert.equal(v.deployment.returnData,'0x');assert.equal(v.deployment.runtimeCodeSha256,v.runtimeSha256);assert.equal(v.deployment.runtimeCodeBytes,v.runtimeCodeBytes);
 assert.ok(v.deployment.steps>0&&v.deployment.steps<=STEP_LIMIT);assert.ok(BigInt(v.deployment.gasUsed)>=0n&&BigInt(v.deployment.gasUsed)<=INITIAL_GAS);
 assert.equal(v.observed.length,vectors.length);
 for(let i=0;i<vectors.length;i++){const a=v.observed[i],x=vectors[i];assert.equal(a.signature,x.signature);assert.equal(a.calldata,v.encodedCalls[i]);assert.equal(a.failed,x.failure);assert.equal(a.exception,x.failure?'revert':null);assert.deepEqual(a.values,x.expected);assert.equal(a.returnData,x.returnData);assert.deepEqual(a.storage,x.storage);assert.deepEqual(a.logs,[]);assert.ok(a.steps>0&&a.steps<=STEP_LIMIT);assert.ok(BigInt(a.gasUsed)>=0n&&BigInt(a.gasUsed)<=INITIAL_GAS);}
}
export function assertOwnedBoolDynamicReport(r){assert.equal(r.status,'working');assert.deepEqual(r.variants.map(x=>x.viaIR),[false,true]);r.variants.forEach(assertOwnedBoolDynamicVariant);}
export async function replayOwnedBoolDynamic(compile,onVariant=()=>{}){
 const source=readFileSync(new URL('./OwnedBoolDynamic.sol',import.meta.url),'utf8'),variants=[];
 for(const viaIR of [false,true]){
  const input={language:'Solidity',sources:{'OwnedBoolDynamic.sol':{content:source}},settings:{viaIR,evmVersion:'osaka',optimizer:{enabled:false,runs:200},metadata:{appendCBOR:false},outputSelection:{'*':{'':['ast'],'*':['abi','evm.bytecode.object','evm.deployedBytecode.object','evm.methodIdentifiers','storageLayout','transientStorageLayout']}}}};
  const output=compile(input),errors=(output.errors??[]).filter(x=>x.severity==='error');if(errors.length){variants.push({viaIR,status:'blocked',errors});continue;}
  const a=output.contracts['OwnedBoolDynamic.sol'].OwnedBoolDynamic,vm=await machine(STEP_LIMIT),observed=[];
  const made=await vm.call({data:Uint8Array.from(Buffer.from(a.evm.bytecode.object,'hex'))}),deployment=creationObservation(made.result.execResult,'constructor',made.metrics);assert.ok(made.result.createdAddress);
  for(const x of vectors){const calldata='0x'+a.evm.methodIdentifiers[x.signature],receipt=await vm.call({to:made.result.createdAddress,data:Uint8Array.from(Buffer.from(calldata.slice(2),'hex'))});const storage=[];for(const slot of [0n,H,H+1n,1n,2n]){const b=await vm.evm.stateManager.getStorage(made.result.createdAddress,Buffer.from(slot.toString(16).padStart(64,'0'),'hex'));storage.push(b.length?BigInt('0x'+hex(b)).toString():'0');}observed.push({...observation(receipt.result.execResult,x.signature,receipt.metrics),calldata,storage,logs:(receipt.result.execResult.logs??[]).map(([a,t,b])=>[hex(a),t.map(hex),hex(b)])});}
  const v={viaIR,status:'working',dataRoot:H.toString(),inputSha256:sha(JSON.stringify(input)),sourceSha256:sha(source),creationSha256:sha(Buffer.from(a.evm.bytecode.object,'hex')),runtimeSha256:sha(Buffer.from(a.evm.deployedBytecode.object,'hex')),runtimeCodeBytes:a.evm.deployedBytecode.object.length/2,storageLayout:a.storageLayout,transientStorageLayout:a.transientStorageLayout,methodIdentifiers:a.evm.methodIdentifiers,encodedCalls:vectors.map(x=>'0x'+a.evm.methodIdentifiers[x.signature]),initialGas:INITIAL_GAS.toString(),stepLimit:STEP_LIMIT,vectors,deployment,observed};onVariant(v);assertOwnedBoolDynamicVariant(v);variants.push(v);
 }
 const r={status:variants.every(x=>x.status==='working')?'working':'blocked',kind:'external-reference-only',boundary:'Finite cross-slot bool34 aliases, dirty owned tails, shrink/regrow, raw payload changes, static/full revert and rollback; not kernel source/compiler or global retained-alias adequacy.',variants};if(r.status==='working')assertOwnedBoolDynamicReport(r);return r;
}
