// VY2 narrow declaration-packing evidence. Public reference APIs/budgets unchanged.
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {machine,observation,creationObservation,INITIAL_GAS,STEP_LIMIT} from '../../scripts/evm-reference/replay.mjs';
const sha=x=>createHash('sha256').update(x).digest('hex');
const selectors={'failAfterWrite()':'3e532498','readAll()':'41f654f7','writeForward()':'a3d251fa','writeReverse()':'891c1b9c'};
const abi=xs=>'0x'+xs.map(x=>BigInt(x).toString(16).padStart(64,'0')).join('');
const pad=(hex,shift)=>BigInt('0x'+hex)*256n**BigInt(shift);
const Z=pad('a5'.repeat(6),26),P3=pad('deadbeef',2),P4=pad('cccc',30),P5=pad('dd'.repeat(26),6),P6=pad('bb'.repeat(6),26);
const fields=(flag,n,b,a)=>BigInt(flag)+BigInt(n)*256n+BigInt(b)*256n**3n+BigInt(a)*256n**6n;
const initial=[Z,0n,0n,P3,P4,P5,P6,55n];
function expected(reverse){
 const arr=Array.from({length:12},(_,i)=>BigInt(i+(reverse?101:1)));
 const ar0=arr.slice(0,10).reduce((x,v,i)=>x+v*256n**BigInt(i*3),P4);
 const ar1=arr.slice(10).reduce((x,v,i)=>x+v*256n**BigInt(i*3),P5);
 return [Z+(reverse?fields(0,0xbeef,0x112233,0xabcdefabcdefabcdefabcdefabcdefabcdefabcdn):fields(1,0x1234,0xff00aa,0x1234567890123456789012345678901234567890n)),
 reverse?1n:(1n<<256n)-1n,reverse?0x180n:(((1n<<248n)-1n)*256n+0x7fn),P3+BigInt(reverse?0xcafe:0xbeef),ar0,ar1,
 P6+(reverse?fields(0,0x3333,0xabcdef,0x43):fields(1,0x2222,0x123456,0x42)),55n].map(String);
}
const revert='0x08c379a0'+(32n).toString(16).padStart(64,'0')+(7n).toString(16).padStart(64,'0')+Buffer.from('packing').toString('hex').padEnd(64,'0');
export const vectors=[['readAll()',initial.map(String)],['writeForward()',expected(false)],['readAll()',expected(false)],['writeReverse()',expected(true)],['readAll()',expected(true)],['failAfterWrite()',[]],['readAll()',expected(true)]].map(([signature,expected])=>({signature,args:[],failure:signature==='failAfterWrite()',expected}));
function layout(l){
 assert.deepEqual(l.storage.map(x=>[x.label,x.slot,x.offset]),[['state','0',0],['composite','4',0],['marker','7',0]]);
 const packed=l.types[l.storage[0].type],composite=l.types[l.storage[1].type];
 assert.equal(l.types[composite.members[0].type].label,'uint24[12]');assert.equal(l.types[l.types[composite.members[0].type].base].numberOfBytes,'3');
 assert.equal(packed.numberOfBytes,'128');assert.equal(composite.numberOfBytes,'96');
 assert.deepEqual(packed.members.map(x=>[x.label,x.slot,x.offset,l.types[x.type].numberOfBytes]),[['flag','0',0,'1'],['small','0',1,'2'],['data','0',3,'3'],['who','0',6,'20'],['wide','1',0,'32'],['one','2',0,'1'],['full','2',1,'31'],['afterValue','3',0,'2']]);
 assert.deepEqual(composite.members.map(x=>[x.label,x.slot,x.offset,l.types[x.type].numberOfBytes]),[['values','0',0,'64'],['inner','2',0,'32']]);
 const inner=l.types[composite.members[1].type];assert.deepEqual(inner.members.map(x=>[x.label,x.slot,x.offset,l.types[x.type].numberOfBytes]),[['flag','0',0,'1'],['small','0',1,'2'],['data','0',3,'3'],['who','0',6,'20']]);
}
export function assertDeclarationVariant(v){
 for(const k of ['inputSha256','sourceSha256','creationSha256','runtimeSha256'])assert.match(v[k],/^[0-9a-f]{64}$/);
 assert.equal(v.status,'working');assert.equal(v.initialGas,'100000000');assert.equal(v.stepLimit,5000000);assert.ok(Number.isSafeInteger(v.runtimeCodeBytes)&&v.runtimeCodeBytes>0);
 assert.deepEqual(v.methodIdentifiers,selectors);assert.equal(v.sourceSha256,sha(readFileSync(new URL('./DeclarationPacking.sol',import.meta.url))));
 layout(v.storageLayout);assert.deepEqual(v.vectors,vectors);assert.equal(v.observed.length,7);assert.deepEqual(v.encodedCalls,vectors.map(x=>'0x'+v.methodIdentifiers[x.signature]));
 assert.equal(v.deployment.failed,false);assert.equal(v.deployment.exception,null);assert.equal(v.deployment.returnData,'0x');assert.equal(v.deployment.runtimeCodeSha256,v.runtimeSha256);assert.equal(v.deployment.runtimeCodeBytes,v.runtimeCodeBytes);
 for(let i=0;i<7;i++){const a=v.observed[i],x=vectors[i];assert.equal(a.signature,x.signature);assert.equal(a.calldata,v.encodedCalls[i]);assert.equal(a.failed,x.failure);assert.equal(a.exception,x.failure?'revert':null);assert.deepEqual(a.values,x.expected);assert.equal(a.returnData,x.failure?revert:abi(x.expected));assert.ok(a.steps>0&&a.steps<=STEP_LIMIT);assert.ok(BigInt(a.gasUsed)>=0n&&BigInt(a.gasUsed)<=INITIAL_GAS);}
 assert.ok(v.deployment.steps>0&&v.deployment.steps<=STEP_LIMIT);assert.ok(BigInt(v.deployment.gasUsed)>=0n&&BigInt(v.deployment.gasUsed)<=INITIAL_GAS);
}
export function assertDeclarationReport(r){assert.equal(r.status,'working');assert.deepEqual(r.variants.map(x=>x.viaIR),[false,true]);r.variants.forEach(assertDeclarationVariant);}
export async function replayDeclarationPacking(compile,onVariant=()=>{}){
 const source=readFileSync(new URL('./DeclarationPacking.sol',import.meta.url),'utf8'),variants=[];
 for(const viaIR of [false,true]){
  const input={language:'Solidity',sources:{'DeclarationPacking.sol':{content:source}},settings:{viaIR,evmVersion:'osaka',optimizer:{enabled:false,runs:200},metadata:{appendCBOR:false},outputSelection:{'*':{'*':['abi','evm.bytecode.object','evm.deployedBytecode.object','evm.methodIdentifiers','storageLayout']}}}};
  const output=compile(input),errors=(output.errors??[]).filter(x=>x.severity==='error');if(errors.length){variants.push({viaIR,status:'blocked',errors});continue;}
  const a=output.contracts['DeclarationPacking.sol'].DeclarationPacking,vm=await machine(STEP_LIMIT),observed=[];
  const made=await vm.call({data:Uint8Array.from(Buffer.from(a.evm.bytecode.object,'hex'))}),deployment=creationObservation(made.result.execResult,'constructor',made.metrics);assert.ok(made.result.createdAddress);
  for(const x of vectors){const calldata='0x'+a.evm.methodIdentifiers[x.signature],receipt=await vm.call({to:made.result.createdAddress,data:Uint8Array.from(Buffer.from(calldata.slice(2),'hex'))});observed.push({...observation(receipt.result.execResult,x.signature,receipt.metrics),calldata});}
  const v={viaIR,status:'working',inputSha256:sha(JSON.stringify(input)),sourceSha256:sha(source),creationSha256:sha(Buffer.from(a.evm.bytecode.object,'hex')),runtimeSha256:sha(Buffer.from(a.evm.deployedBytecode.object,'hex')),runtimeCodeBytes:a.evm.deployedBytecode.object.length/2,storageLayout:a.storageLayout,methodIdentifiers:a.evm.methodIdentifiers,encodedCalls:vectors.map(x=>'0x'+a.evm.methodIdentifiers[x.signature]),initialGas:INITIAL_GAS.toString(),stepLimit:STEP_LIMIT,vectors,deployment,observed};onVariant(v);assertDeclarationVariant(v);variants.push(v);
 }
 const r={status:variants.every(x=>x.status==='working')?'working':'blocked',kind:'external-reference-only',boundary:'Declared packed scalar/array/struct positions, complete raw words/padding/order/revert; no universal source/compiler adequacy.',variants};if(r.status==='working')assertDeclarationReport(r);return r;
}
