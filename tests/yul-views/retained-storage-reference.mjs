// Independent finite expectations; actual source/kernel state is separate.
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {createRequire} from 'node:module';
const {keccak_256}=await import(createRequire(new URL('../../scripts/evm-reference/replay.mjs',import.meta.url)).resolve('@noble/hashes/sha3.js'));
import {machine,observation,creationObservation,INITIAL_GAS,STEP_LIMIT} from '../../scripts/evm-reference/replay.mjs';
const hex=x=>Buffer.from(x).toString('hex'),sha=x=>createHash('sha256').update(x).digest('hex');
const W=1n<<256n,P=1n<<240n,abi=xs=>'0x'+xs.map(x=>BigInt(x).toString(16).padStart(64,'0')).join('');
const hash=n=>BigInt('0x'+hex(keccak_256(Buffer.from(BigInt(n).toString(16).padStart(64,'0'),'hex'))));
const H=hash(0),X=hash(H+1n),Y=hash(H+3n),roots=[H,X,Y],slots=[0n,H+1n,X,H,H+3n,Y,1n,2n];
for(const r of roots)assert.ok(r>3n&&r+4n<W);
for(let i=0;i<roots.length;i++)for(let j=0;j<i;j++)assert.ok(roots[i]>roots[j]?roots[i]-roots[j]>4n:roots[j]-roots[i]>4n);
const DATA=P+77n+(88n<<16n)+(77n<<32n);
function raw(outer=2,length=2,marker=0){return [outer,length,DATA,P+12n,1,55,777,marker].map(String);}
function error(s){return '0x08c379a0'+(32n).toString(16).padStart(64,'0')+BigInt(s.length).toString(16).padStart(64,'0')+Buffer.from(s).toString('hex').padEnd(64,'0');}
function tupleReason(words,reason){return abi([...words,(words.length+1)*32,(reason.length-2)/2])+reason.slice(2).padEnd(Math.ceil((reason.length-2)/64)*64,'0');}
const wordsOf=h=>h.slice(2).match(/.{64}/g).map(x=>BigInt('0x'+x).toString());
const child=error('child'),outer=error('outer'),panic='0x4e487b71'+(50n).toString(16).padStart(64,'0');
const runBytes=tupleReason([0,3,77,12,1,777,0,DATA],child);
export const vectors=[
 ['snap()',abi(raw()),false,raw()],['run()',runBytes,false,raw(0,3,1)],['snap()',abi(raw(0,3,1)),false,raw(0,3,1)],
 ['restore()',abi(raw(2,3,1)),false,raw(2,3,1)],['successThenOuterRevert()',outer,true,raw(2,3,1)],['snap()',abi(raw(2,3,1)),false,raw(2,3,1)],
 ['staticProbe()',abi([0,0]),false,raw(2,3,1)],['snap()',abi(raw(2,3,1)),false,raw(2,3,1)],['bounds()',panic,true,raw(2,3,1)],
 ['snap()',abi(raw(2,3,1)),false,raw(2,3,1)],['run()',runBytes,false,raw(0,3,1)],['snap()',abi(raw(0,3,1)),false,raw(0,3,1)]]
 .map(([signature,returnData,failure,storage])=>({signature,args:[],expected:failure?[]:wordsOf(returnData),failure,returnData,storage}));
const names=['snap()','run()','restore()','childFail()','childSuccess()','successThenOuterRevert()','attemptWrite()','staticProbe()','bounds()'];
const selectors=Object.fromEntries(names.map(s=>[s,hex(keccak_256(Buffer.from(s))).slice(0,8)]));
export function assertRetainedVariant(v){
 assert.equal(v.status,'working');assert.equal(v.initialGas,'100000000');assert.equal(v.stepLimit,5000000);
 for(const k of ['inputSha256','sourceSha256','creationSha256','runtimeSha256'])assert.match(v[k],/^[0-9a-f]{64}$/);
 assert.equal(v.sourceSha256,sha(readFileSync(new URL('./RetainedStorage.sol',import.meta.url))));
 assert.ok(Number.isSafeInteger(v.runtimeCodeBytes)&&v.runtimeCodeBytes>0);
 assert.deepEqual(v.methodIdentifiers,selectors);assert.deepEqual(v.vectors,vectors);assert.deepEqual(v.encodedCalls,vectors.map(x=>'0x'+selectors[x.signature]));
 assert.deepEqual(v.storageLayout.storage.map(x=>[x.label,x.slot,x.offset]),[['nodes','0',0],['guard','1',0],['marker','2',0]]);
 const t=v.storageLayout.types,n=t[t[v.storageLayout.storage[0].type].base];assert.equal(n.numberOfBytes,'64');assert.deepEqual(n.members.map(x=>[x.label,x.slot,x.offset]),[['stamp','0',0],['xs','1',0]]);
 assert.deepEqual(v.transientStorageLayout.storage,[]);assert.deepEqual(v.dataRoots,roots.map(String));
 assert.equal(v.deployment.failed,false);assert.equal(v.deployment.exception,null);assert.equal(v.deployment.returnData,'0x');assert.equal(v.deployment.runtimeCodeSha256,v.runtimeSha256);assert.equal(v.deployment.runtimeCodeBytes,v.runtimeCodeBytes);
 assert.ok(v.deployment.steps>0&&v.deployment.steps<=STEP_LIMIT);assert.ok(BigInt(v.deployment.gasUsed)>=0n&&BigInt(v.deployment.gasUsed)<=INITIAL_GAS);
 assert.equal(v.observed.length,vectors.length);
 for(let i=0;i<vectors.length;i++){const a=v.observed[i],x=vectors[i];assert.equal(a.signature,x.signature);assert.equal(a.calldata,v.encodedCalls[i]);assert.equal(a.failed,x.failure);assert.equal(a.exception,x.failure?'revert':null);assert.deepEqual(a.values,x.expected);assert.equal(a.returnData,x.returnData);assert.deepEqual(a.storage,x.storage);assert.deepEqual(a.logs,[]);assert.ok(a.steps>0&&a.steps<=STEP_LIMIT);assert.ok(BigInt(a.gasUsed)>=0n&&BigInt(a.gasUsed)<=INITIAL_GAS);}
}
export function assertRetainedReport(r){assert.equal(r.status,'working');assert.deepEqual(r.variants.map(x=>x.viaIR),[false,true]);r.variants.forEach(assertRetainedVariant);}
export async function replayRetained(compile,onVariant=()=>{}){
 const source=readFileSync(new URL('./RetainedStorage.sol',import.meta.url),'utf8'),variants=[];
 for(const viaIR of [false,true]){
  const input={language:'Solidity',sources:{'RetainedStorage.sol':{content:source}},settings:{viaIR,evmVersion:'osaka',optimizer:{enabled:false,runs:200},metadata:{appendCBOR:false},outputSelection:{'*':{'':['ast'],'*':['abi','evm.bytecode.object','evm.deployedBytecode.object','evm.methodIdentifiers','storageLayout','transientStorageLayout']}}}};
  const output=compile(input),errors=(output.errors??[]).filter(x=>x.severity==='error');if(errors.length){variants.push({viaIR,status:'blocked',errors});continue;}
  const a=output.contracts['RetainedStorage.sol'].RetainedStorage,vm=await machine(STEP_LIMIT),observed=[];
  const made=await vm.call({data:Uint8Array.from(Buffer.from(a.evm.bytecode.object,'hex'))}),deployment=creationObservation(made.result.execResult,'constructor',made.metrics);assert.ok(made.result.createdAddress);
  for(const x of vectors){const calldata='0x'+a.evm.methodIdentifiers[x.signature],receipt=await vm.call({to:made.result.createdAddress,data:Uint8Array.from(Buffer.from(calldata.slice(2),'hex'))});const storage=[];for(const slot of slots){const b=await vm.evm.stateManager.getStorage(made.result.createdAddress,Buffer.from(slot.toString(16).padStart(64,'0'),'hex'));storage.push(b.length?BigInt('0x'+hex(b)).toString():'0');}observed.push({...observation(receipt.result.execResult,x.signature,receipt.metrics),calldata,storage,logs:(receipt.result.execResult.logs??[]).map(([a,t,b])=>[hex(a),t.map(hex),hex(b)])});}
  const v={viaIR,status:'working',inputSha256:sha(JSON.stringify(input)),sourceSha256:sha(source),creationSha256:sha(Buffer.from(a.evm.bytecode.object,'hex')),runtimeSha256:sha(Buffer.from(a.evm.deployedBytecode.object,'hex')),runtimeCodeBytes:a.evm.deployedBytecode.object.length/2,storageLayout:a.storageLayout,transientStorageLayout:a.transientStorageLayout,dataRoots:roots.map(String),methodIdentifiers:a.evm.methodIdentifiers,encodedCalls:vectors.map(x=>'0x'+a.evm.methodIdentifiers[x.signature]),initialGas:INITIAL_GAS.toString(),stepLimit:STEP_LIMIT,vectors,deployment,observed};onVariant(v);assertRetainedVariant(v);variants.push(v);
 }
 const r={status:variants.every(x=>x.status==='working')?'working':'blocked',kind:'external-reference-only',boundary:'Finite actual caller aliases suspended across no-reference helpers, nested revert/commit, full ABI/errors/storage; not kernel/source/compiler or whole-history adequacy.',variants};if(r.status==='working')assertRetainedReport(r);return r;
}
