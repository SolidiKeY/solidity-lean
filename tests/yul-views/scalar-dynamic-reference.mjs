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
const HX=hash(0),HY=hash(2),HZ=hash(3),MAX=(1n<<256n)-1n;
const W=1n<<256n,word=n=>(BigInt(n)+W)%W;
const pack=(xs,bits)=>xs.reduce((sum,n,i)=>sum+(BigInt(n)<<BigInt(bits*i)),0n);
const initialX=Array.from({length:32},(_,i)=>i%2);
const initialY=[0x010203,0xabcdef,0,0xffffff,0x800000,1,0x112233,0x445566,0x778899,0xfedcba];
const X1=(BigInt('0x'+'cc'.repeat(28))<<32n)+0x020101n;
const Y1=(BigInt('0x'+'dd'.repeat(26))<<48n)+0x112233ffffffn;
const AP=[0x1234n,(1n<<160n)-1n,0x1122334455667788990011223344556677889900n];
for(const h of [HX,HY,HZ]){assert.ok(h+3n<W);for(const r of [0n,1n,2n,3n,4n])assert.ok(r<h||r>=h+3n);}
for(const [a,b] of [[HX,HY],[HX,HZ],[HY,HZ]])assert.ok(a>b?a-b>=3n:b-a>=3n);
const names=['readAll()','fill()','shrinkOne()','zero()','regrow()','writeMembers()','failAfterWrite()','outOfBounds()','staticProbe()','readTyped()','dirtyGrow()','restore()'];
const selectors=Object.fromEntries(names.map(x=>[x,hex(keccak_256(Buffer.from(x))).slice(0,8)]));
function values(stage){
 const nx={initial:0,fill:33,one:1,zero:0,regrow:34,members:34,dirty:35}[stage];
 const ny={initial:0,fill:11,one:1,zero:0,regrow:12,members:12,dirty:12}[stage];
 const nz={initial:0,fill:2,one:1,zero:0,regrow:3,members:3,dirty:3}[stage];
 const changed=stage==='members'||stage==='dirty',x=[...initialX],y=[...initialY],a=[...AP];
 if(changed){x[0]=1;x[31]=0;y[0]=0xa1b2c3;y[9]=1;a[0]=(1n<<160n)-1n;a[1]=0n;}
 const tx=changed?[0,1]:[1,1],ty=changed?[0x010203,0x112233]:[0xffffff,0x112233];
 const rx=pack(x,8),rt=(X1>>16n<<16n)+pack(tx,8),ry=(0xaabbn<<240n)+pack(y,24),ryt=(Y1>>48n<<48n)+pack(ty,24);
 return [nx,nx,ny,nz,nx?x[0]:0,nx>31?x[31]:0,nx>32?tx[0]:0,nx>33?tx[1]:0,
 ny?y[0]:0,ny>9?y[9]:0,ny>10?ty[0]:0,ny>11?ty[1]:0,nz?a[0]:0,nz>1?a[1]:0,nz>2?a[2]:0,
 changed?555:0,nx,ny,nz,rx,rt,ry,ryt,(BigInt('0x'+'aa'.repeat(12))<<160n)+a[0],(BigInt('0x'+'bb'.repeat(12))<<160n)+a[1],(BigInt('0x'+'cc'.repeat(12))<<160n)+a[2],999,HX,HY,HZ,0,2,3,ny>1?y[1]:0,nx>1?x[1]:0,nx>34?1:0].map(n=>String(word(n)));
}
const error='0x08c379a0'+(32n).toString(16).padStart(64,'0')+(6n).toString(16).padStart(64,'0')+Buffer.from('scalar').toString('hex').padEnd(64,'0');
const panic='0x4e487b71'+(0x32n).toString(16).padStart(64,'0');
export const vectors=[['readAll()',values('initial')],['fill()',values('fill')],['readAll()',values('fill')],
 ['shrinkOne()',values('one')],['readAll()',values('one')],['zero()',values('zero')],['readAll()',values('zero')],
 ['regrow()',values('regrow')],['readAll()',values('regrow')],['readTyped()',[(0x010203n<<232n).toString(),String(AP[0]),'0']],
 ['writeMembers()',values('members')],['readTyped()',[(0xa1b2c3n<<232n).toString(),String((1n<<160n)-1n),'1']],['readAll()',values('members')],
 ['dirtyGrow()',values('dirty')],['readAll()',values('dirty')],['restore()',values('members')],
 ['failAfterWrite()',[],error],['readAll()',values('members')],['outOfBounds()',[],panic],['staticProbe()',['0']],['readAll()',values('members')]
].map(([signature,expected,revertData])=>({signature,args:[],failure:!!revertData,revertData:revertData??'0x',expected:!revertData&&!['staticProbe()','readTyped()'].includes(signature)?['32','36',...expected]:expected}));
function layout(v){
 assert.deepEqual(v.storageLayout.storage.map(x=>[x.label,x.slot,x.offset,v.storageLayout.types[x.type].numberOfBytes]),[['xs','0',0,'32'],['marker','1',0,'32'],['ys','2',0,'32'],['zs','3',0,'32']]);
 for(const [i,label,width] of [[0,'bool','1'],[2,'bytes3','3'],[3,'address','20']]){const t=v.storageLayout.types[v.storageLayout.storage[i].type];assert.equal(t.encoding,'dynamic_array');assert.equal(v.storageLayout.types[t.base].label,label);assert.equal(v.storageLayout.types[t.base].numberOfBytes,width);}
 assert.deepEqual(v.transientStorageLayout.storage,[]);
}
export function assertScalarDynamicVariant(v){
 assert.equal(v.status,'working');assert.equal(v.initialGas,'100000000');assert.equal(v.stepLimit,5000000);
 for(const k of ['inputSha256','sourceSha256','creationSha256','runtimeSha256'])assert.match(v[k],/^[0-9a-f]{64}$/);
 assert.equal(v.sourceSha256,sha(readFileSync(new URL('./ScalarDynamic.sol',import.meta.url))));
 assert.ok(Number.isSafeInteger(v.runtimeCodeBytes)&&v.runtimeCodeBytes>0);assert.deepEqual(v.methodIdentifiers,selectors);layout(v);
 assert.deepEqual(v.hashInputs,[0n,2n,3n].map(n=>n.toString(16).padStart(64,'0')));assert.deepEqual(v.dataRoots,[String(HX),String(HY),String(HZ)]);
 assert.deepEqual(v.vectors,vectors);assert.deepEqual(v.encodedCalls,vectors.map(x=>'0x'+selectors[x.signature]));assert.equal(v.observed.length,21);
 assert.equal(v.deployment.failed,false);assert.equal(v.deployment.exception,null);assert.equal(v.deployment.returnData,'0x');assert.equal(v.deployment.runtimeCodeSha256,v.runtimeSha256);assert.equal(v.deployment.runtimeCodeBytes,v.runtimeCodeBytes);
 assert.ok(v.deployment.steps>0&&v.deployment.steps<=STEP_LIMIT);assert.ok(BigInt(v.deployment.gasUsed)>=0n&&BigInt(v.deployment.gasUsed)<=INITIAL_GAS);
 for(let i=0;i<vectors.length;i++){const a=v.observed[i],x=vectors[i];assert.equal(a.signature,x.signature);assert.equal(a.calldata,v.encodedCalls[i]);assert.equal(a.failed,x.failure);assert.equal(a.exception,x.failure?'revert':null);assert.deepEqual(a.values,x.expected);assert.equal(a.returnData,x.failure?x.revertData:abi(x.expected));assert.ok(a.steps>0&&a.steps<=STEP_LIMIT);assert.ok(BigInt(a.gasUsed)>=0n&&BigInt(a.gasUsed)<=INITIAL_GAS);}
}
export function assertScalarDynamicReport(r){assert.equal(r.status,'working');assert.deepEqual(r.variants.map(x=>x.viaIR),[false,true]);r.variants.forEach(assertScalarDynamicVariant);}
export async function replayScalarDynamic(compile,onVariant=()=>{}){
 const source=readFileSync(new URL('./ScalarDynamic.sol',import.meta.url),'utf8'),variants=[];
 for(const viaIR of [false,true]){
  const input={language:'Solidity',sources:{'ScalarDynamic.sol':{content:source}},settings:{viaIR,evmVersion:'osaka',optimizer:{enabled:false,runs:200},metadata:{appendCBOR:false},outputSelection:{'*':{'':['ast'],'*':['abi','evm.bytecode.object','evm.deployedBytecode.object','evm.methodIdentifiers','storageLayout','transientStorageLayout']}}}};
  const output=compile(input),errors=(output.errors??[]).filter(x=>x.severity==='error');if(errors.length){variants.push({viaIR,status:'blocked',errors});continue;}
  const a=output.contracts['ScalarDynamic.sol'].ScalarDynamic,vm=await machine(STEP_LIMIT),observed=[];
  const made=await vm.call({data:Uint8Array.from(Buffer.from(a.evm.bytecode.object,'hex'))}),deployment=creationObservation(made.result.execResult,'constructor',made.metrics);assert.ok(made.result.createdAddress);
  for(const x of vectors){const calldata='0x'+a.evm.methodIdentifiers[x.signature],receipt=await vm.call({to:made.result.createdAddress,data:Uint8Array.from(Buffer.from(calldata.slice(2),'hex'))});observed.push({...observation(receipt.result.execResult,x.signature,receipt.metrics),calldata});}
  const v={viaIR,status:'working',inputSha256:sha(JSON.stringify(input)),sourceSha256:sha(source),creationSha256:sha(Buffer.from(a.evm.bytecode.object,'hex')),runtimeSha256:sha(Buffer.from(a.evm.deployedBytecode.object,'hex')),runtimeCodeBytes:a.evm.deployedBytecode.object.length/2,storageLayout:a.storageLayout,transientStorageLayout:a.transientStorageLayout,hashInputs:[0,2,3].map(n=>BigInt(n).toString(16).padStart(64,'0')),dataRoots:[String(HX),String(HY),String(HZ)],methodIdentifiers:a.evm.methodIdentifiers,encodedCalls:vectors.map(x=>'0x'+a.evm.methodIdentifiers[x.signature]),initialGas:INITIAL_GAS.toString(),stepLimit:STEP_LIMIT,vectors,deployment,observed};onVariant(v);assertScalarDynamicVariant(v);variants.push(v);
 }
 const r={status:variants.every(x=>x.status==='working')?'working':'blocked',kind:'external-reference-only',boundary:'Finite bool/bytes3/address storage and distinct ABI alignment, raw dirty bool growth, header/alias/padding/tail/static/failure observations; no kernel/source/compiler or allocation adequacy.',variants};if(r.status==='working')assertScalarDynamicReport(r);return r;
}
