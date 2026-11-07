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
const H=[1,2,4].map(hash),W=1n<<256n,MAX=W-1n,word=n=>(BigInt(n)+W)%W;
const X1=(BigInt('0x'+'cc'.repeat(28))<<32n)+(0x8000n<<16n)+77n;
const Y1=(BigInt('0x'+'dd'.repeat(24))<<48n)+(0x800000n<<24n)+77n;
const B0=(BigInt('0x'+'ee'.repeat(28))<<32n)+0x02010101n;
const R0=(0xa5n<<248n)+0x1234n,R3=(0xaan<<248n)+(0x1234n<<24n)+0x010203n;
for(const h of H){assert.ok(h+2n<W);assert.ok(h>6n);}
for(let i=0;i<H.length;i++)for(let j=0;j<i;j++)assert.ok(H[i]>H[j]?H[i]-H[j]>=2n:H[j]-H[i]>=2n);
const names=['readAll()','fill()','shrink()','regrow()','aliases()','dirtyGrow()','restore()','failAfterWrite()','outOfBounds()','staticProbe()'];
const selectors=Object.fromEntries(names.map(x=>[x,hex(keccak_256(Buffer.from(x))).slice(0,8)]));
function values(stage){
 const x={initial:0,fill:17,zero:0,regrow:18,alias:18,dirty:18}[stage],y={initial:0,fill:11,zero:0,regrow:12,alias:12,dirty:12}[stage];
 const b=stage==='initial'?0:stage==='dirty'?4:3,changed=['alias','dirty'].includes(stage);
 const xword=(X1>>16n<<16n)+(changed?88n:77n),yword=(Y1>>48n<<48n)+((changed?0xffffffn:0x800000n)<<24n)+77n,bword=B0-(changed?1n:0n);
 return [x,x,y,b,x?65535:0,x>16?(changed?88:77):0,x>17?32768:0,y?MAX:0,y>9?MAX:0,y>10?77:0,b?(changed?0:1):0,b>2?1:0,b>3?1:0,0x1234,0x010203,0x1234,changed?222:0,x,y,b,R0,R3,MAX,xword,MAX,yword,bword,999,...H].map(n=>String(word(n)));
}
const error='0x08c379a0'+(32n).toString(16).padStart(64,'0')+(6n).toString(16).padStart(64,'0')+Buffer.from('nested').toString('hex').padEnd(64,'0');
const panic='0x4e487b71'+(0x32n).toString(16).padStart(64,'0');
export const vectors=[['readAll()',values('initial')],['fill()',values('fill')],['readAll()',values('fill')],['shrink()',values('zero')],['readAll()',values('zero')],['regrow()',values('regrow')],['readAll()',values('regrow')],['aliases()',values('alias')],['readAll()',values('alias')],['dirtyGrow()',values('dirty')],['readAll()',values('dirty')],['restore()',values('alias')],['failAfterWrite()',[],error],['readAll()',values('alias')],['outOfBounds()',[],panic],['staticProbe()',['0']],['readAll()',values('alias')]]
 .map(([signature,expected,revertData])=>({signature,args:[],failure:!!revertData,revertData:revertData??'0x',expected:!revertData&&signature!=='staticProbe()'?['32','31',...expected]:expected}));
function layout(v){
 assert.deepEqual(v.storageLayout.storage.map(x=>[x.label,x.slot,x.offset]),[['box','0',0],['top','4',0],['marker','5',0]]);
 const s=v.storageLayout.types[v.storageLayout.storage[0].type];assert.equal(s.encoding,'inplace');assert.equal(s.numberOfBytes,'128');
 assert.deepEqual(s.members.map(x=>[x.label,x.slot,x.offset,v.storageLayout.types[x.type].numberOfBytes]),[['guard','0',0,'2'],['xs','1',0,'32'],['ys','2',0,'32'],['tag','3',0,'3'],['who','3',3,'20']]);
 for(const [i,label] of [[1,'uint16'],[2,'int24']]){const t=v.storageLayout.types[s.members[i].type];assert.equal(t.encoding,'dynamic_array');assert.equal(v.storageLayout.types[t.base].label,label);}
 const b=v.storageLayout.types[v.storageLayout.storage[1].type];assert.equal(b.encoding,'dynamic_array');assert.equal(v.storageLayout.types[b.base].label,'bool');assert.deepEqual(v.transientStorageLayout.storage,[]);
}
export function assertNestedDynamicVariant(v){
 assert.equal(v.status,'working');assert.equal(v.initialGas,'100000000');assert.equal(v.stepLimit,5000000);
 for(const k of ['inputSha256','sourceSha256','creationSha256','runtimeSha256'])assert.match(v[k],/^[0-9a-f]{64}$/);
 assert.equal(v.sourceSha256,sha(readFileSync(new URL('./NestedDynamic.sol',import.meta.url))));
 assert.ok(Number.isSafeInteger(v.runtimeCodeBytes)&&v.runtimeCodeBytes>0);assert.deepEqual(v.methodIdentifiers,selectors);layout(v);
 assert.deepEqual(v.hashInputs,[1n,2n,4n].map(n=>n.toString(16).padStart(64,'0')));assert.deepEqual(v.dataRoots,H.map(String));
 assert.deepEqual(v.vectors,vectors);assert.deepEqual(v.encodedCalls,vectors.map(x=>'0x'+selectors[x.signature]));assert.equal(v.observed.length,17);
 assert.equal(v.deployment.failed,false);assert.equal(v.deployment.exception,null);assert.equal(v.deployment.returnData,'0x');assert.equal(v.deployment.runtimeCodeSha256,v.runtimeSha256);assert.equal(v.deployment.runtimeCodeBytes,v.runtimeCodeBytes);
 assert.ok(v.deployment.steps>0&&v.deployment.steps<=STEP_LIMIT);assert.ok(BigInt(v.deployment.gasUsed)>=0n&&BigInt(v.deployment.gasUsed)<=INITIAL_GAS);
 for(let i=0;i<vectors.length;i++){const a=v.observed[i],x=vectors[i];assert.equal(a.signature,x.signature);assert.equal(a.calldata,v.encodedCalls[i]);assert.equal(a.failed,x.failure);assert.equal(a.exception,x.failure?'revert':null);assert.deepEqual(a.values,x.expected);assert.equal(a.returnData,x.failure?x.revertData:abi(x.expected));assert.ok(a.steps>0&&a.steps<=STEP_LIMIT);assert.ok(BigInt(a.gasUsed)>=0n&&BigInt(a.gasUsed)<=INITIAL_GAS);}
}
export function assertNestedDynamicReport(r){assert.equal(r.status,'working');assert.deepEqual(r.variants.map(x=>x.viaIR),[false,true]);r.variants.forEach(assertNestedDynamicVariant);}
export async function replayNestedDynamic(compile,onVariant=()=>{}){
 const source=readFileSync(new URL('./NestedDynamic.sol',import.meta.url),'utf8'),variants=[];
 for(const viaIR of [false,true]){
  const input={language:'Solidity',sources:{'NestedDynamic.sol':{content:source}},settings:{viaIR,evmVersion:'osaka',optimizer:{enabled:false,runs:200},metadata:{appendCBOR:false},outputSelection:{'*':{'':['ast'],'*':['abi','evm.bytecode.object','evm.deployedBytecode.object','evm.methodIdentifiers','storageLayout','transientStorageLayout']}}}};
  const output=compile(input),errors=(output.errors??[]).filter(x=>x.severity==='error');if(errors.length){variants.push({viaIR,status:'blocked',errors});continue;}
  const a=output.contracts['NestedDynamic.sol'].NestedDynamic,vm=await machine(STEP_LIMIT),observed=[];
  const made=await vm.call({data:Uint8Array.from(Buffer.from(a.evm.bytecode.object,'hex'))}),deployment=creationObservation(made.result.execResult,'constructor',made.metrics);assert.ok(made.result.createdAddress);
  for(const x of vectors){const calldata='0x'+a.evm.methodIdentifiers[x.signature],receipt=await vm.call({to:made.result.createdAddress,data:Uint8Array.from(Buffer.from(calldata.slice(2),'hex'))});observed.push({...observation(receipt.result.execResult,x.signature,receipt.metrics),calldata});}
  const v={viaIR,status:'working',inputSha256:sha(JSON.stringify(input)),sourceSha256:sha(source),creationSha256:sha(Buffer.from(a.evm.bytecode.object,'hex')),runtimeSha256:sha(Buffer.from(a.evm.deployedBytecode.object,'hex')),runtimeCodeBytes:a.evm.deployedBytecode.object.length/2,storageLayout:a.storageLayout,transientStorageLayout:a.transientStorageLayout,hashInputs:[1,2,4].map(n=>BigInt(n).toString(16).padStart(64,'0')),dataRoots:H.map(String),methodIdentifiers:a.evm.methodIdentifiers,encodedCalls:vectors.map(x=>'0x'+a.evm.methodIdentifiers[x.signature]),initialGas:INITIAL_GAS.toString(),stepLimit:STEP_LIMIT,vectors,deployment,observed};onVariant(v);assertNestedDynamicVariant(v);variants.push(v);
 }
 const r={status:variants.every(x=>x.status==='working')?'working':'blocked',kind:'external-reference-only',boundary:'Finite mixed integer/scalar nested storage, cross-family writes, raw dirty bool growth, alias/padding/rollback and ABI observations; no kernel/source/compiler or allocation adequacy.',variants};if(r.status==='working')assertNestedDynamicReport(r);return r;
}
