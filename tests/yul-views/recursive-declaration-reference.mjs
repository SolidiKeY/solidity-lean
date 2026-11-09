// VY2 narrow recursive-declaration evidence. Public reference APIs/budgets unchanged.
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {machine,observation,creationObservation,INITIAL_GAS,STEP_LIMIT} from '../../scripts/evm-reference/replay.mjs';
const sha=x=>createHash('sha256').update(x).digest('hex');
const selectors={'failAfterWrite()':'3e532498','readAll()':'41f654f7','writeForward()':'a3d251fa','writeReverse()':'891c1b9c'};
const abi=xs=>'0x'+xs.map(x=>BigInt(x).toString(16).padStart(64,'0')).join('');
const pad=(hex,shift)=>BigInt('0x'+hex)*256n**BigInt(shift);
const P=pad('bb'.repeat(29),3),A=0n,B=pad('dd'.repeat(16),16);
const initial=[P,P,P,P,A,B,55n,777n,888n,...Array(11).fill(0n)];
function expected(reverse){
 const members=Array.from({length:4},(_,n)=>[BigInt(reverse?0:1),BigInt((reverse?0x3333:0x2222)+n)]);
 const raw=members.map(([f,s])=>P+f+s*256n);
 const arr=Array.from({length:3},(_,i)=>BigInt(i+(reverse?101:1)));
 raw.push(arr[0]+arr[1]*256n**16n,B+arr[2]);
 return [...raw,55n,777n,888n,...members.flat(),...arr].map(String);
}
const revert='0x08c379a0'+(32n).toString(16).padStart(64,'0')+(9n).toString(16).padStart(64,'0')+Buffer.from('recursive').toString('hex').padEnd(64,'0');
export const vectors=[['readAll()',initial.map(String)],['writeForward()',expected(false)],['readAll()',expected(false)],['writeReverse()',expected(true)],['readAll()',expected(true)],['failAfterWrite()',[]],['readAll()',expected(true)]].map(([signature,expected])=>({signature,args:[],failure:signature==='failAfterWrite()',expected}));
function layout(l){
 assert.deepEqual(l.storage.map(x=>[x.label,x.slot,x.offset]),[['prefix','0',0],['state','8',0],['marker','14',0]]);
 const root=l.types[l.storage[1].type];assert.equal(root.numberOfBytes,'192');
 assert.deepEqual(root.members.map(x=>[x.label,x.slot,x.offset,l.types[x.type].numberOfBytes]),[['grid','0',0,'128'],['values','4',0,'64']]);
 const outer=l.types[root.members[0].type],innerArray=l.types[outer.base],inner=l.types[innerArray.base];
 assert.equal(outer.numberOfBytes,'128');assert.equal(innerArray.numberOfBytes,'64');assert.equal(inner.numberOfBytes,'32');
 assert.deepEqual(inner.members.map(x=>[x.label,x.slot,x.offset,l.types[x.type].numberOfBytes]),[['flag','0',0,'1'],['small','0',1,'2']]);
 assert.equal(l.types[l.types[root.members[1].type].base].numberOfBytes,'16');
}
export function assertRecursiveDeclarationVariant(v){
 for(const k of ['inputSha256','sourceSha256','creationSha256','runtimeSha256'])assert.match(v[k],/^[0-9a-f]{64}$/);
 assert.equal(v.status,'working');assert.equal(v.initialGas,'100000000');assert.equal(v.stepLimit,5000000);assert.ok(Number.isSafeInteger(v.runtimeCodeBytes)&&v.runtimeCodeBytes>0);
 assert.deepEqual(v.methodIdentifiers,selectors);assert.equal(v.sourceSha256,sha(readFileSync(new URL('./RecursiveDeclaration.sol',import.meta.url))));
 layout(v.storageLayout);assert.deepEqual(v.vectors,vectors);assert.equal(v.observed.length,7);assert.deepEqual(v.encodedCalls,vectors.map(x=>'0x'+v.methodIdentifiers[x.signature]));
 assert.equal(v.deployment.failed,false);assert.equal(v.deployment.exception,null);assert.equal(v.deployment.returnData,'0x');assert.equal(v.deployment.runtimeCodeSha256,v.runtimeSha256);assert.equal(v.deployment.runtimeCodeBytes,v.runtimeCodeBytes);
 for(let i=0;i<7;i++){const a=v.observed[i],x=vectors[i];assert.equal(a.signature,x.signature);assert.equal(a.calldata,v.encodedCalls[i]);assert.equal(a.failed,x.failure);assert.equal(a.exception,x.failure?'revert':null);assert.deepEqual(a.values,x.expected);assert.equal(a.returnData,x.failure?revert:abi(x.expected));assert.ok(a.steps>0&&a.steps<=STEP_LIMIT);assert.ok(BigInt(a.gasUsed)>=0n&&BigInt(a.gasUsed)<=INITIAL_GAS);}
 assert.ok(v.deployment.steps>0&&v.deployment.steps<=STEP_LIMIT);assert.ok(BigInt(v.deployment.gasUsed)>=0n&&BigInt(v.deployment.gasUsed)<=INITIAL_GAS);
}
export function assertRecursiveDeclarationReport(r){assert.equal(r.status,'working');assert.deepEqual(r.variants.map(x=>x.viaIR),[false,true]);r.variants.forEach(assertRecursiveDeclarationVariant);}
export async function replayRecursiveDeclaration(compile,onVariant=()=>{}){
 const source=readFileSync(new URL('./RecursiveDeclaration.sol',import.meta.url),'utf8'),variants=[];
 for(const viaIR of [false,true]){
  const input={language:'Solidity',sources:{'RecursiveDeclaration.sol':{content:source}},settings:{viaIR,evmVersion:'osaka',optimizer:{enabled:false,runs:200},metadata:{appendCBOR:false},outputSelection:{'*':{'*':['abi','evm.bytecode.object','evm.deployedBytecode.object','evm.methodIdentifiers','storageLayout']}}}};
  const output=compile(input),errors=(output.errors??[]).filter(x=>x.severity==='error');if(errors.length){variants.push({viaIR,status:'blocked',errors});continue;}
  const a=output.contracts['RecursiveDeclaration.sol'].RecursiveDeclaration,vm=await machine(STEP_LIMIT),observed=[];
  const made=await vm.call({data:Uint8Array.from(Buffer.from(a.evm.bytecode.object,'hex'))}),deployment=creationObservation(made.result.execResult,'constructor',made.metrics);assert.ok(made.result.createdAddress);
  for(const x of vectors){const calldata='0x'+a.evm.methodIdentifiers[x.signature],receipt=await vm.call({to:made.result.createdAddress,data:Uint8Array.from(Buffer.from(calldata.slice(2),'hex'))});observed.push({...observation(receipt.result.execResult,x.signature,receipt.metrics),calldata});}
  const v={viaIR,status:'working',inputSha256:sha(JSON.stringify(input)),sourceSha256:sha(source),creationSha256:sha(Buffer.from(a.evm.bytecode.object,'hex')),runtimeSha256:sha(Buffer.from(a.evm.deployedBytecode.object,'hex')),runtimeCodeBytes:a.evm.deployedBytecode.object.length/2,storageLayout:a.storageLayout,methodIdentifiers:a.evm.methodIdentifiers,encodedCalls:vectors.map(x=>'0x'+a.evm.methodIdentifiers[x.signature]),initialGas:INITIAL_GAS.toString(),stepLimit:STEP_LIMIT,vectors,deployment,observed};onVariant(v);assertRecursiveDeclarationVariant(v);variants.push(v);
 }
 const r={status:variants.every(x=>x.status==='working')?'working':'blocked',kind:'external-reference-only',boundary:'Recursive fixed-array/struct positions, complete raw words/padding/order/revert; no universal source/compiler adequacy.',variants};if(r.status==='working')assertRecursiveDeclarationReport(r);return r;
}
