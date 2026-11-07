// VY2 narrow root-sequence evidence. Public reference APIs/budgets unchanged.
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {machine,observation,creationObservation,INITIAL_GAS,STEP_LIMIT} from '../../scripts/evm-reference/replay.mjs';
const sha=x=>createHash('sha256').update(x).digest('hex');
const selectors={'failAfterWrite()':'3e532498','readAll()':'41f654f7','writeForward()':'a3d251fa','writeReverse()':'891c1b9c'};
const abi=xs=>'0x'+xs.map(x=>BigInt(x).toString(16).padStart(64,'0')).join('');
const pad=(hex,shift)=>BigInt('0x'+hex)*256n**BigInt(shift);
const C=pad('aa'.repeat(31),1),I=pad('bb'.repeat(29),3),E=pad('ee',31),F=pad('cc'.repeat(30),2),T=pad('dd'.repeat(30),2),MAX=(1n<<248n)-1n;
const initial=[0n,C,I,I,E,F,55n,999n,...Array(9).fill(0n),55n,0n,0n];
function expected(reverse,transient=false){
 const a=reverse?18n:17n,b=reverse?MAX-1n:MAX,c=reverse?0n:1n;
 const flags=reverse?0n:1n,s0=reverse?0x3333n:0x2222n,s1=s0+1n,e=reverse?0x123456n:0x9876n,f=reverse?0x4567n:0x3456n,t=reverse?0x9999n:0x7788n;
 return [a+b*256n,C+c,I+flags+s0*256n,I+flags+s1*256n,E+e,F+f,55n,999n,
 a,b,c,flags,s0,flags,s1,e,f,55n,transient?t:0n,transient?T+t:0n].map(String);
}
const revert='0x08c379a0'+(32n).toString(16).padStart(64,'0')+(11n).toString(16).padStart(64,'0')+Buffer.from('root layout').toString('hex').padEnd(64,'0');
export const vectors=[['readAll()',initial.map(String)],['writeForward()',expected(false,true)],['readAll()',expected(false)],['writeReverse()',expected(true,true)],['readAll()',expected(true)],['failAfterWrite()',[]],['readAll()',expected(true)]].map(([signature,expected])=>({signature,args:[],failure:signature==='failAfterWrite()',expected}));
function layout(l,t){
 assert.deepEqual(l.storage.map(x=>[x.label,x.slot,x.offset]),[['a','0',0],['b','0',1],['c','1',0],['items','2',0],['e','4',0],['f','5',0],['marker','6',0]]);
 assert.deepEqual(l.storage.map(x=>l.types[x.type].numberOfBytes),['1','31','1','64','31','2','32']);
 const arr=l.types[l.storage[3].type],inner=l.types[arr.base];assert.equal(inner.numberOfBytes,'32');
 assert.deepEqual(inner.members.map(x=>[x.label,x.slot,x.offset,l.types[x.type].numberOfBytes]),[['flag','0',0,'1'],['small','0',1,'2']]);
 assert.deepEqual(t.storage.map(x=>[x.label,x.slot,x.offset,t.types[x.type].numberOfBytes]),[['temp','0',0,'2']]);
}
export function assertRootSequenceVariant(v){
 for(const k of ['inputSha256','sourceSha256','creationSha256','runtimeSha256'])assert.match(v[k],/^[0-9a-f]{64}$/);
 assert.equal(v.status,'working');assert.equal(v.initialGas,'100000000');assert.equal(v.stepLimit,5000000);assert.ok(Number.isSafeInteger(v.runtimeCodeBytes)&&v.runtimeCodeBytes>0);
 assert.deepEqual(v.methodIdentifiers,selectors);assert.equal(v.sourceSha256,sha(readFileSync(new URL('./RootSequence.sol',import.meta.url))));
 layout(v.storageLayout,v.transientStorageLayout);assert.deepEqual(v.vectors,vectors);assert.equal(v.observed.length,7);assert.deepEqual(v.encodedCalls,vectors.map(x=>'0x'+v.methodIdentifiers[x.signature]));
 assert.equal(v.deployment.failed,false);assert.equal(v.deployment.exception,null);assert.equal(v.deployment.returnData,'0x');assert.equal(v.deployment.runtimeCodeSha256,v.runtimeSha256);assert.equal(v.deployment.runtimeCodeBytes,v.runtimeCodeBytes);
 for(let i=0;i<7;i++){const a=v.observed[i],x=vectors[i];assert.equal(a.signature,x.signature);assert.equal(a.calldata,v.encodedCalls[i]);assert.equal(a.failed,x.failure);assert.equal(a.exception,x.failure?'revert':null);assert.deepEqual(a.values,x.expected);assert.equal(a.returnData,x.failure?revert:abi(x.expected));assert.ok(a.steps>0&&a.steps<=STEP_LIMIT);assert.ok(BigInt(a.gasUsed)>=0n&&BigInt(a.gasUsed)<=INITIAL_GAS);}
 assert.ok(v.deployment.steps>0&&v.deployment.steps<=STEP_LIMIT);assert.ok(BigInt(v.deployment.gasUsed)>=0n&&BigInt(v.deployment.gasUsed)<=INITIAL_GAS);
}
export function assertRootSequenceReport(r){assert.equal(r.status,'working');assert.deepEqual(r.variants.map(x=>x.viaIR),[false,true]);r.variants.forEach(assertRootSequenceVariant);}
export async function replayRootSequence(compile,onVariant=()=>{}){
 const source=readFileSync(new URL('./RootSequence.sol',import.meta.url),'utf8'),variants=[];
 for(const viaIR of [false,true]){
  const input={language:'Solidity',sources:{'RootSequence.sol':{content:source}},settings:{viaIR,evmVersion:'osaka',optimizer:{enabled:false,runs:200},metadata:{appendCBOR:false},outputSelection:{'*':{'*':['abi','evm.bytecode.object','evm.deployedBytecode.object','evm.methodIdentifiers','storageLayout','transientStorageLayout']}}}};
  const output=compile(input),errors=(output.errors??[]).filter(x=>x.severity==='error');if(errors.length){variants.push({viaIR,status:'blocked',errors});continue;}
  const a=output.contracts['RootSequence.sol'].RootSequence,vm=await machine(STEP_LIMIT),observed=[];
  const made=await vm.call({data:Uint8Array.from(Buffer.from(a.evm.bytecode.object,'hex'))}),deployment=creationObservation(made.result.execResult,'constructor',made.metrics);assert.ok(made.result.createdAddress);
  for(const x of vectors){const calldata='0x'+a.evm.methodIdentifiers[x.signature],receipt=await vm.call({to:made.result.createdAddress,data:Uint8Array.from(Buffer.from(calldata.slice(2),'hex'))});observed.push({...observation(receipt.result.execResult,x.signature,receipt.metrics),calldata});}
  const v={viaIR,status:'working',inputSha256:sha(JSON.stringify(input)),sourceSha256:sha(source),creationSha256:sha(Buffer.from(a.evm.bytecode.object,'hex')),runtimeSha256:sha(Buffer.from(a.evm.deployedBytecode.object,'hex')),runtimeCodeBytes:a.evm.deployedBytecode.object.length/2,storageLayout:a.storageLayout,transientStorageLayout:a.transientStorageLayout,methodIdentifiers:a.evm.methodIdentifiers,encodedCalls:vectors.map(x=>'0x'+a.evm.methodIdentifiers[x.signature]),initialGas:INITIAL_GAS.toString(),stepLimit:STEP_LIMIT,vectors,deployment,observed};onVariant(v);assertRootSequenceVariant(v);variants.push(v);
 }
 const r={status:variants.every(x=>x.status==='working')?'working':'blocked',kind:'external-reference-only',boundary:'Ordered scalar roots plus nested fixed array, separate transient bank, complete raw words/padding/order/revert; no universal source/compiler adequacy.',variants};if(r.status==='working')assertRootSequenceReport(r);return r;
}
