// Finite pinned external controls; no kernel/source/compiler adequacy claim.
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {createRequire} from 'node:module';
const {keccak_256}=await import(createRequire(new URL('../../scripts/evm-reference/replay.mjs',import.meta.url)).resolve('@noble/hashes/sha3.js'));
import {machine,observation,creationObservation,INITIAL_GAS,STEP_LIMIT} from '../../scripts/evm-reference/replay.mjs';
const sha=x=>createHash('sha256').update(x).digest('hex'),hex=x=>Buffer.from(x).toString('hex');
const abi=xs=>'0x'+xs.map(x=>BigInt(x).toString(16).padStart(64,'0')).join('');
const hash=n=>BigInt('0x'+hex(keccak_256(Buffer.from(BigInt(n).toString(16).padStart(64,'0'),'hex'))));
const HX=hash(0),HY=hash(2),MAX=(1n<<256n)-1n;
const X1=BigInt('0x'+'cc'.repeat(30)+'004d'),Y0=BigInt('0xaabb'+'ff'.repeat(30)),Y1=BigInt('0x'+'dd'.repeat(29)+'000063');
assert.ok(HX!==HY&&HX+2n<(1n<<256n)&&HY+2n<(1n<<256n));
assert.ok(HX>HY?HX-HY>=2n:HY-HX>=2n);
for(const h of [HX,HY])for(const r of [0n,1n,2n,3n])assert.ok(r<h||r>=h+2n);
const names=['readAll()','fill()','shrinkOne()','zero()','regrow()','writeMembers()','failAfterWrite()','outOfBounds()','staticProbe()'];
const selectors=Object.fromEntries(names.map(x=>[x,hex(keccak_256(Buffer.from(x))).slice(0,8)]));
function values(stage){
 const nx={initial:0,fill:17,one:1,zero:0,regrow:18,members:18}[stage];
 const ny={initial:0,fill:11,one:1,zero:0,regrow:11,members:11}[stage],changed=stage==='members';
 const x0=changed?MAX-(1n<<240n):MAX,x1=changed?X1+1n:X1,y0=changed?Y0-((0xffffffn-0x123456n)<<216n):Y0;
 return [nx,nx,ny,ny,nx?65535:0,nx>15?(changed?65534:65535):0,nx>16?(changed?78:77):0,nx>17?0xcccc:0,
 ny?0xffffff:0,ny>9?(changed?0x123456:0xffffff):0,ny>10?99:0,changed?555:0,
 nx,ny,x0,x1,y0,Y1,999,HX,HY,0,2].map(String);
}
const error='0x08c379a0'+(32n).toString(16).padStart(64,'0')+(6n).toString(16).padStart(64,'0')+Buffer.from('packed').toString('hex').padEnd(64,'0');
const panic='0x4e487b71'+(0x32n).toString(16).padStart(64,'0');
export const vectors=[['readAll()',values('initial')],['fill()',values('fill')],['readAll()',values('fill')],
 ['shrinkOne()',values('one')],['readAll()',values('one')],['zero()',values('zero')],['readAll()',values('zero')],
 ['regrow()',values('regrow')],['readAll()',values('regrow')],['writeMembers()',values('members')],['readAll()',values('members')],
 ['failAfterWrite()',[],error],['readAll()',values('members')],['outOfBounds()',[],panic],['staticProbe()',['0']],['readAll()',values('members')]
].map(([signature,expected,revertData])=>({signature,args:[],failure:!!revertData,revertData:revertData??'0x',expected:!revertData&&signature!=='staticProbe()'?['32','23',...expected]:expected}));
function layout(v){
 assert.deepEqual(v.storageLayout.storage.map(x=>[x.label,x.slot,x.offset,v.storageLayout.types[x.type].numberOfBytes]),[['xs','0',0,'32'],['marker','1',0,'32'],['ys','2',0,'32']]);
 for(const [i,label,width] of [[0,'uint16','2'],[2,'uint24','3']]){const t=v.storageLayout.types[v.storageLayout.storage[i].type];assert.equal(t.encoding,'dynamic_array');assert.equal(v.storageLayout.types[t.base].label,label);assert.equal(v.storageLayout.types[t.base].numberOfBytes,width);}
 assert.deepEqual(v.transientStorageLayout.storage,[]);
}
export function assertPackedDynamicVariant(v){
 assert.equal(v.status,'working');assert.equal(v.initialGas,'100000000');assert.equal(v.stepLimit,5000000);
 for(const k of ['inputSha256','sourceSha256','creationSha256','runtimeSha256'])assert.match(v[k],/^[0-9a-f]{64}$/);
 assert.equal(v.sourceSha256,sha(readFileSync(new URL('./PackedDynamic.sol',import.meta.url))));
 assert.ok(Number.isSafeInteger(v.runtimeCodeBytes)&&v.runtimeCodeBytes>0);assert.deepEqual(v.methodIdentifiers,selectors);layout(v);
 assert.deepEqual(v.hashInputs,[(0n).toString(16).padStart(64,'0'),(2n).toString(16).padStart(64,'0')]);assert.deepEqual(v.dataRoots,[String(HX),String(HY)]);
 assert.deepEqual(v.vectors,vectors);assert.deepEqual(v.encodedCalls,vectors.map(x=>'0x'+selectors[x.signature]));assert.equal(v.observed.length,16);
 assert.equal(v.deployment.failed,false);assert.equal(v.deployment.exception,null);assert.equal(v.deployment.returnData,'0x');assert.equal(v.deployment.runtimeCodeSha256,v.runtimeSha256);assert.equal(v.deployment.runtimeCodeBytes,v.runtimeCodeBytes);
 assert.ok(v.deployment.steps>0&&v.deployment.steps<=STEP_LIMIT);assert.ok(BigInt(v.deployment.gasUsed)>=0n&&BigInt(v.deployment.gasUsed)<=INITIAL_GAS);
 for(let i=0;i<vectors.length;i++){const a=v.observed[i],x=vectors[i];assert.equal(a.signature,x.signature);assert.equal(a.calldata,v.encodedCalls[i]);assert.equal(a.failed,x.failure);assert.equal(a.exception,x.failure?'revert':null);assert.deepEqual(a.values,x.expected);assert.equal(a.returnData,x.failure?x.revertData:abi(x.expected));assert.ok(a.steps>0&&a.steps<=STEP_LIMIT);assert.ok(BigInt(a.gasUsed)>=0n&&BigInt(a.gasUsed)<=INITIAL_GAS);}
}
export function assertPackedDynamicReport(r){assert.equal(r.status,'working');assert.deepEqual(r.variants.map(x=>x.viaIR),[false,true]);r.variants.forEach(assertPackedDynamicVariant);}
export async function replayPackedDynamic(compile,onVariant=()=>{}){
 const source=readFileSync(new URL('./PackedDynamic.sol',import.meta.url),'utf8'),variants=[];
 for(const viaIR of [false,true]){
  const input={language:'Solidity',sources:{'PackedDynamic.sol':{content:source}},settings:{viaIR,evmVersion:'osaka',optimizer:{enabled:false,runs:200},metadata:{appendCBOR:false},outputSelection:{'*':{'':['ast'],'*':['abi','evm.bytecode.object','evm.deployedBytecode.object','evm.methodIdentifiers','storageLayout','transientStorageLayout']}}}};
  const output=compile(input),errors=(output.errors??[]).filter(x=>x.severity==='error');if(errors.length){variants.push({viaIR,status:'blocked',errors});continue;}
  const a=output.contracts['PackedDynamic.sol'].PackedDynamic,vm=await machine(STEP_LIMIT),observed=[];
  const made=await vm.call({data:Uint8Array.from(Buffer.from(a.evm.bytecode.object,'hex'))}),deployment=creationObservation(made.result.execResult,'constructor',made.metrics);assert.ok(made.result.createdAddress);
  for(const x of vectors){const calldata='0x'+a.evm.methodIdentifiers[x.signature],receipt=await vm.call({to:made.result.createdAddress,data:Uint8Array.from(Buffer.from(calldata.slice(2),'hex'))});observed.push({...observation(receipt.result.execResult,x.signature,receipt.metrics),calldata});}
  const v={viaIR,status:'working',inputSha256:sha(JSON.stringify(input)),sourceSha256:sha(source),creationSha256:sha(Buffer.from(a.evm.bytecode.object,'hex')),runtimeSha256:sha(Buffer.from(a.evm.deployedBytecode.object,'hex')),runtimeCodeBytes:a.evm.deployedBytecode.object.length/2,storageLayout:a.storageLayout,transientStorageLayout:a.transientStorageLayout,hashInputs:[0,2].map(n=>BigInt(n).toString(16).padStart(64,'0')),dataRoots:[String(HX),String(HY)],methodIdentifiers:a.evm.methodIdentifiers,encodedCalls:vectors.map(x=>'0x'+a.evm.methodIdentifiers[x.signature]),initialGas:INITIAL_GAS.toString(),stepLimit:STEP_LIMIT,vectors,deployment,observed};onVariant(v);assertPackedDynamicVariant(v);variants.push(v);
 }
 const r={status:variants.every(x=>x.status==='working')?'working':'blocked',kind:'external-reference-only',boundary:'Finite packed unsigned uint16/uint24 storage/header/alias/padding/tail/static/failure observations; no kernel/source/compiler or allocation adequacy.',variants};if(r.status==='working')assertPackedDynamicReport(r);return r;
}
