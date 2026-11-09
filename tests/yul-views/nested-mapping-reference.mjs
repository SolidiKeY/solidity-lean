import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {createRequire} from 'node:module';
import {machine,observation,creationObservation,INITIAL_GAS,STEP_LIMIT} from '../../scripts/evm-reference/replay.mjs';
const {keccak_256}=await import(createRequire(new URL('../../scripts/evm-reference/replay.mjs',import.meta.url)).resolve('@noble/hashes/sha3.js'));
const hex=x=>Buffer.from(x).toString('hex'),sha=x=>createHash('sha256').update(x).digest('hex');
const W=1n<<256n;
export const abi=xs=>'0x'+xs.map(x=>{const n=BigInt(x);assert.ok(n>=0n&&n<W);return n.toString(16).padStart(64,'0');}).join('');
const reason=s=>'0x08c379a0'+abi([32,Buffer.byteLength(s)]).slice(2)+Buffer.from(s).toString('hex').padEnd(64,'0');
const signatures=['state()','read(uint256,uint256)','put(uint256,uint256,uint256,bool)','same(uint256,uint256)','probe()','seed()'];
const selectors=Object.fromEntries(signatures.map(s=>[s,hex(keccak_256(Buffer.from(s))).slice(0,8)]));
const hash=(k,p)=>BigInt('0x'+hex(keccak_256(Buffer.from(abi([k,p]).slice(2),'hex'))));
const parent=k=>hash(k,0),slot=(o,i)=>hash(i,parent(o));
const vector=(signature,args,expected,marker,root,x,y,z,gap=0,failure=false,returnData=null)=>({signature,args:args.map(String),expected:expected.map(String),storage:[root,marker,x,y,z,gap].map(String),failure,returnData:returnData??abi(expected)});
const read=(o,i,v,m,r,x,y,z,g=0)=>vector('read(uint256,uint256)',[o,i],[v,v,parent(o),slot(o,i)],m,r,x,y,z,g);
const state=(m,r,x,y,z,g=0)=>vector('state()',[],[m,r,x,y,z],m,r,x,y,z,g);
const put=(o,i,v,m,r,x,y,z,g=0)=>vector('put(uint256,uint256,uint256,bool)',[o,i,v,0],[v,v,parent(o),slot(o,i)],m,r,x,y,z,g);
export const vectors=[state(0,0,0,0,0),read(1,2,0,0,0,0,0,0),
 put(1,2,77,1,0,77,0,0),put(1,3,999,2,0,77,999,0),put(2,2,W-1n,3,0,77,999,W-1n),
 state(3,0,77,999,W-1n),read(2,1,0,3,0,77,999,W-1n),
 vector('put(uint256,uint256,uint256,bool)',[1,2,888,1],[],3,0,77,999,W-1n,0,true,reason('nested mapping')),
 state(3,0,77,999,W-1n),vector('same(uint256,uint256)',[1,2],[77],3,0,77,999,W-1n),
 vector('probe()',[],[0,64,0],3,0,77,999,W-1n),state(3,0,77,999,W-1n),
 vector('seed()',[],[165],3,165,77,999,W-1n,4243),read(1,2,77,3,165,77,999,W-1n,4243),
 put(1,2,0,4,165,0,999,W-1n,4243),state(4,165,0,999,W-1n,4243)];
const encoded=x=>'0x'+selectors[x.signature]+abi(x.args).slice(2);
const inputFor=(viaIR,source)=> ({language:'Solidity',sources:{'NestedMapping.sol':{content:source}},settings:{viaIR,evmVersion:'osaka',optimizer:{enabled:false,runs:200},metadata:{appendCBOR:false},outputSelection:{'*':{'':['ast'],'*':['abi','evm.bytecode.object','evm.deployedBytecode.object','evm.methodIdentifiers','storageLayout','transientStorageLayout','ir','irOptimized']}}}});
export function assertNestedMappingVariant(v){
 assert.equal(v.status,'working');assert.equal(v.initialGas,'100000000');assert.equal(v.stepLimit,5000000);
 for(const k of ['inputSha256','sourceSha256','creationSha256','runtimeSha256'])assert.match(v[k],/^[0-9a-f]{64}$/);
 const source=readFileSync(new URL('./NestedMapping.sol',import.meta.url),'utf8');assert.equal(v.sourceSha256,sha(source));
 assert.equal(v.inputSha256,sha(JSON.stringify(inputFor(v.viaIR,source))));
 assert.ok(Number.isSafeInteger(v.runtimeCodeBytes)&&v.runtimeCodeBytes>0);
 assert.deepEqual(v.methodIdentifiers,selectors);assert.deepEqual(v.vectors,vectors);assert.deepEqual(v.encodedCalls,vectors.map(encoded));
 assert.deepEqual(v.storageLayout.storage.map(x=>[x.label,x.slot,x.offset]),[['table','0',0],['marker','1',0]]);assert.deepEqual(v.transientStorageLayout.storage.map(x=>[x.label,x.slot,x.offset]),[]);
 assert.equal(v.deployment.failed,false);assert.equal(v.deployment.exception,null);assert.equal(v.deployment.returnData,'0x');
 assert.equal(v.deployment.runtimeCodeSha256,v.runtimeSha256);assert.equal(v.deployment.runtimeCodeBytes,v.runtimeCodeBytes);
 assert.ok(v.deployment.steps>0&&v.deployment.steps<=STEP_LIMIT);assert.ok(BigInt(v.deployment.gasUsed)>=0n&&BigInt(v.deployment.gasUsed)<=INITIAL_GAS);
 assert.equal(v.observed.length,vectors.length);
 for(let i=0;i<vectors.length;i++){
  const x=vectors[i],z=v.observed[i];assert.equal(z.signature,x.signature);assert.equal(z.calldata,v.encodedCalls[i]);
  assert.equal(z.failed,x.failure);assert.equal(z.exception,x.failure?'revert':null);assert.deepEqual(z.values,x.expected);assert.equal(z.returnData,x.returnData);
  assert.deepEqual(z.storage,x.storage);assert.deepEqual(z.logs,[]);assert.ok(z.steps>0&&z.steps<=STEP_LIMIT);
  assert.ok(Number.isSafeInteger(z.maxStack)&&z.maxStack>=0&&z.maxStack<=1024);assert.ok(BigInt(z.gasUsed)>=0n&&BigInt(z.gasUsed)<=INITIAL_GAS);
 }
}
export function assertNestedMappingReport(r){assert.equal(r.status,'working');assert.deepEqual(r.variants.map(v=>v.viaIR),[false,true]);r.variants.forEach(assertNestedMappingVariant);}
export async function replayNestedMapping(compile,onVariant=()=>{}){
 const source=readFileSync(new URL('./NestedMapping.sol',import.meta.url),'utf8'),variants=[];
 for(const viaIR of [false,true]){
  const input=inputFor(viaIR,source);
  const output=compile(input),errors=(output.errors??[]).filter(x=>x.severity==='error');if(errors.length){variants.push({viaIR,status:'blocked',errors});onVariant(variants.at(-1));continue;}
  const artifact=output.contracts['NestedMapping.sol'].NestedMapping,vm=await machine(STEP_LIMIT),observed=[];
  const made=await vm.call({data:Uint8Array.from(Buffer.from(artifact.evm.bytecode.object,'hex'))}),deployment=creationObservation(made.result.execResult,'constructor',made.metrics);assert.ok(made.result.createdAddress);
  for(const x of vectors){const calldata=encoded(x),receipt=await vm.call({to:made.result.createdAddress,data:Uint8Array.from(Buffer.from(calldata.slice(2),'hex'))});const stored=[];for(const qslot of [0,1,slot(1,2),slot(1,3),slot(2,2),79]){const key=Buffer.from(BigInt(qslot).toString(16).padStart(64,'0'),'hex');const bytes=await vm.evm.stateManager.getStorage(made.result.createdAddress,key);stored.push(bytes.length?BigInt('0x'+hex(bytes)).toString():'0');}observed.push({...observation(receipt.result.execResult,x.signature,receipt.metrics),calldata,storage:stored,logs:(receipt.result.execResult.logs??[]).map(([a,t,b])=>[hex(a),t.map(hex),hex(b)])});}
  const v={viaIR,status:'working',inputSha256:sha(JSON.stringify(input)),sourceSha256:sha(source),creationSha256:sha(Buffer.from(artifact.evm.bytecode.object,'hex')),runtimeSha256:sha(Buffer.from(artifact.evm.deployedBytecode.object,'hex')),runtimeCodeBytes:artifact.evm.deployedBytecode.object.length/2,storageLayout:artifact.storageLayout,transientStorageLayout:artifact.transientStorageLayout,methodIdentifiers:artifact.evm.methodIdentifiers,encodedCalls:vectors.map(encoded),initialGas:INITIAL_GAS.toString(),stepLimit:STEP_LIMIT,vectors,deployment,observed,ir:artifact.ir,irOptimized:artifact.irOptimized};onVariant(v);assertNestedMappingVariant(v);variants.push(v);
 }
 const report={status:variants.every(v=>v.status==='working')?'working':'blocked',kind:'external-reference-only',boundary:'Finite nested word-key mapping exact-keccak parent/leaf slots, shared-prefix/sibling isolation, unchanged SSTORE, static refusal, revert restoration and residual root/gap preservation. Not frontend admission, seeded kernel equality, arbitrary memory safety or source/compiler/target adequacy.',variants};if(report.status==='working')assertNestedMappingReport(report);return report;
}
