// Finite pinned external evidence; independent expected raw words and ABI.
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {createRequire} from 'node:module';
const {keccak_256}=await import(createRequire(new URL('../../scripts/evm-reference/replay.mjs',import.meta.url)).resolve('@noble/hashes/sha3.js'));
import {machine,observation,creationObservation,INITIAL_GAS,STEP_LIMIT} from '../../scripts/evm-reference/replay.mjs';
const hex=x=>Buffer.from(x).toString('hex'),sha=x=>createHash('sha256').update(x).digest('hex');
const W=1n<<256n,P=1n<<240n,MAX=W-1n,abi=xs=>'0x'+xs.map(x=>BigInt(x).toString(16).padStart(64,'0')).join('');
const hash=n=>BigInt('0x'+hex(keccak_256(Buffer.from(BigInt(n).toString(16).padStart(64,'0'),'hex'))));
const H=hash(0),G=hash(1),roots=[H,G,hash(H+1n),hash(H+2n),hash(H+3n),hash(H+5n),hash(G),hash(G+1n)];
for(const r of roots)assert.ok(r>3n&&r+8n<W);
for(let i=0;i<roots.length;i++)for(let j=0;j<i;j++)assert.ok(roots[i]>roots[j]?roots[i]-roots[j]>8n:roots[j]-roots[i]>8n);
const X=P+77n+(88n<<16n)+(99n<<32n),Y=P+0xffffffn,B=P+1n;
function raw(outer=2,length=2,marker=0,changed=false){return [outer,2,marker,P+12n,length,changed?X+(35n<<16n):X,Y,B,P+13n,1,1,P+33n,P+44n,1,55].map(String);}
const err='0x08c379a0'+(32n).toString(16).padStart(64,'0')+(9n).toString(16).padStart(64,'0')+Buffer.from('aggregate').toString('hex').padEnd(64,'0');
const panic='0x4e487b71'+(50n).toString(16).padStart(64,'0');
export const vectors=[['snap()',raw()],['retainedAlias()',[0,3,99,12,0xffffff,77].map(String)],['snap()',raw(0,3,77)],['restore()',raw(2,3,77)],['innerShrink()',raw(2,0,77)],['snap()',raw(2,0,77)],['innerRegrow()',raw(2,3,77,true)],['typed()',[3,77,123,99,MAX,1,33,44,55].map(String)],['failAfterWrite()',[],err],['snap()',raw(2,3,77,true)],['bounds()',[],panic],['staticProbe()',['0']],['snap()',raw(2,3,77,true)]]
.map(([signature,expected,revertData])=>({signature,args:[],expected,failure:!!revertData,revertData:revertData??'0x'}));
const selectors=Object.fromEntries(vectors.map(x=>[x.signature,hex(keccak_256(Buffer.from(x.signature))).slice(0,8)]));
export function assertAggregateVariant(v){
 assert.equal(v.status,'working');assert.equal(v.initialGas,'100000000');assert.equal(v.stepLimit,5000000);
 for(const k of ['inputSha256','sourceSha256','creationSha256','runtimeSha256'])assert.match(v[k],/^[0-9a-f]{64}$/);
 assert.equal(v.sourceSha256,sha(readFileSync(new URL('./AggregateDynamic.sol',import.meta.url))));
 assert.ok(Number.isSafeInteger(v.runtimeCodeBytes)&&v.runtimeCodeBytes>0);
 assert.deepEqual(v.methodIdentifiers,selectors);assert.deepEqual(v.vectors,vectors);assert.deepEqual(v.encodedCalls,vectors.map(x=>'0x'+selectors[x.signature]));
 assert.deepEqual(v.storageLayout.storage.map(x=>[x.label,x.slot,x.offset]),[['nodes','0',0],['grid','1',0],['marker','2',0]]);
 const t=v.storageLayout.types,n=t[t[v.storageLayout.storage[0].type].base];assert.equal(n.numberOfBytes,'128');assert.deepEqual(n.members.map(x=>[x.label,x.slot,x.offset]),[['stamp','0',0],['xs','1',0],['ys','2',0],['bs','3',0]]);
 assert.deepEqual(v.transientStorageLayout.storage,[]);assert.deepEqual(v.dataRoots,roots.map(String));
 assert.equal(v.deployment.failed,false);assert.equal(v.deployment.exception,null);assert.equal(v.deployment.returnData,'0x');assert.equal(v.deployment.runtimeCodeSha256,v.runtimeSha256);assert.equal(v.deployment.runtimeCodeBytes,v.runtimeCodeBytes);
 assert.ok(v.deployment.steps>0&&v.deployment.steps<=STEP_LIMIT);assert.ok(BigInt(v.deployment.gasUsed)>=0n&&BigInt(v.deployment.gasUsed)<=INITIAL_GAS);
 assert.equal(v.observed.length,vectors.length);
 for(let i=0;i<vectors.length;i++){const a=v.observed[i],x=vectors[i];assert.equal(a.signature,x.signature);assert.equal(a.calldata,v.encodedCalls[i]);assert.equal(a.failed,x.failure);assert.equal(a.exception,x.failure?'revert':null);assert.deepEqual(a.values,x.expected);assert.equal(a.returnData,x.failure?x.revertData:abi(x.expected));assert.ok(a.steps>0&&a.steps<=STEP_LIMIT);assert.ok(BigInt(a.gasUsed)>=0n&&BigInt(a.gasUsed)<=INITIAL_GAS);}
}
export function assertAggregateReport(r){assert.equal(r.status,'working');assert.deepEqual(r.variants.map(x=>x.viaIR),[false,true]);r.variants.forEach(assertAggregateVariant);}
export async function replayAggregate(compile,onVariant=()=>{}){
 const source=readFileSync(new URL('./AggregateDynamic.sol',import.meta.url),'utf8'),variants=[];
 for(const viaIR of [false,true]){
  const input={language:'Solidity',sources:{'AggregateDynamic.sol':{content:source}},settings:{viaIR,evmVersion:'osaka',optimizer:{enabled:false,runs:200},metadata:{appendCBOR:false},outputSelection:{'*':{'':['ast'],'*':['abi','evm.bytecode.object','evm.deployedBytecode.object','evm.methodIdentifiers','storageLayout','transientStorageLayout']}}}};
  const output=compile(input),errors=(output.errors??[]).filter(x=>x.severity==='error');if(errors.length){variants.push({viaIR,status:'blocked',errors});continue;}
  const a=output.contracts['AggregateDynamic.sol'].AggregateDynamic,vm=await machine(STEP_LIMIT),observed=[];
  const made=await vm.call({data:Uint8Array.from(Buffer.from(a.evm.bytecode.object,'hex'))}),deployment=creationObservation(made.result.execResult,'constructor',made.metrics);assert.ok(made.result.createdAddress);
  for(const x of vectors){const calldata='0x'+a.evm.methodIdentifiers[x.signature],receipt=await vm.call({to:made.result.createdAddress,data:Uint8Array.from(Buffer.from(calldata.slice(2),'hex'))});observed.push({...observation(receipt.result.execResult,x.signature,receipt.metrics),calldata});}
  const v={viaIR,status:'working',inputSha256:sha(JSON.stringify(input)),sourceSha256:sha(source),creationSha256:sha(Buffer.from(a.evm.bytecode.object,'hex')),runtimeSha256:sha(Buffer.from(a.evm.deployedBytecode.object,'hex')),runtimeCodeBytes:a.evm.deployedBytecode.object.length/2,storageLayout:a.storageLayout,transientStorageLayout:a.transientStorageLayout,dataRoots:roots.map(String),methodIdentifiers:a.evm.methodIdentifiers,encodedCalls:vectors.map(x=>'0x'+a.evm.methodIdentifiers[x.signature]),initialGas:INITIAL_GAS.toString(),stepLimit:STEP_LIMIT,vectors,deployment,observed};onVariant(v);assertAggregateVariant(v);variants.push(v);
 }
 const r={status:variants.every(x=>x.status==='working')?'working':'blocked',kind:'external-reference-only',boundary:'Finite aggregate arrays/nested arrays and retained alias observations, not kernel/source/compiler or whole-ownership adequacy.',variants};if(r.status==='working')assertAggregateReport(r);return r;
}
