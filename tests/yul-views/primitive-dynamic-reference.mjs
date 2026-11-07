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
const H=[0,1,2,3,4,5].map(hash),W=1n<<256n,MAX=W-1n,word=n=>(BigInt(n)+W)%W;
const pack=(vs,bits)=>vs.reduce((v,n,i)=>v+((word(n)%(1n<<BigInt(bits)))<<BigInt(bits*i)),0n);
const S=[-1,-32768,32767,0,...Array(11).fill(-4370),-1],U=[1,0xffffff,0x800000,0,7,8,9,10,11,0x112233];
const S1=(BigInt('0x'+'cc'.repeat(28))<<32n)+(0x8000n<<16n)+77n;
const U1=(BigInt('0x'+'dd'.repeat(29))<<24n)+77n;
const B0=(BigInt('0x'+'ee'.repeat(28))<<32n)+0x02010100n;
const Y0=(BigInt('0x'+'f4'.repeat(23))<<72n)+(77n<<48n)+(0xaabbccn<<24n)+0x010203n;
const Z0=(BigInt('0x'+'aa'.repeat(12))<<160n)+0x1234n,Z1=(BigInt('0x'+'bb'.repeat(12))<<160n)+(1n<<160n)-1n;
for(const h of H){assert.ok(h+2n<W);for(let r=0n;r<=7n;r++)assert.ok(r<h||r>=h+2n);}
for(let i=0;i<6;i++)for(let j=0;j<i;j++)assert.ok(H[i]>H[j]?H[i]-H[j]>=2n:H[j]-H[i]>=2n);
const names=['readAll()','fill()','writeBool()','shrinkOne()','zero()','regrow()','writeSigned()','writeMembers()','dirtyGrow()','restore()','failAfterWrite()','outOfBounds()','staticProbe()','readTyped()'];
const selectors=Object.fromEntries(names.map(x=>[x,hex(keccak_256(Buffer.from(x))).slice(0,8)]));
function values(stage){
 const live=stage!=='initial',ss={initial:0,fill:17,bool:17,one:1,zero:0,regrow:18,signed:18,members:18,dirty:18}[stage];
 const bs={initial:0,fill:3,bool:3,one:1,zero:0,regrow:3,signed:3,members:3,dirty:4}[stage];
 const bc=live&&stage!=='fill',sc=['signed','members','dirty'].includes(stage),mc=['members','dirty'].includes(stage);
 const sv=[...S],uv=[...U];if(sc)sv[0]=-32768;if(mc)uv[0]=2;
 const st=sc?-1:-32768,rawS1=(S1>>32n<<32n)+pack([77,st],16),rawB=B0+(bc?1n:0n);
 const rawY=(Y0>>24n<<24n)+BigInt(mc?0xa1b2c3:0x010203),rawZ=(Z0>>160n<<160n)+(mc?(1n<<160n)-1n:0x1234n);
 const lens=[ss,live?11:0,live?2:0,bs,live?3:0,live?2:0],marker=mc?555:sc?222:bc?111:0;
 return [ss,ss,lens[1],lens[2],bs,bs,lens[4],lens[5],ss?sv[0]:0,ss>16?77:0,ss>17?st:0,live?uv[0]:0,live?uv[9]:0,live?77:0,live?(mc?55:MAX):0,live?77:0,bs?(bc?1:0):0,bs>1?1:0,bs>2?1:0,bs>3?1:0,live?(mc?0xa1b2c3:0x010203):0,live?77:0,live?(mc?(1n<<160n)-1n:0x1234n):0,live?(1n<<160n)-1n:0,marker,...lens,pack(sv,16),rawS1,(0xabcdn<<240n)+pack(uv,24),U1,mc?55:MAX,77,rawB,rawY,rawZ,Z1,999,...H,0,3,4,5].map(n=>String(word(n)));
}
const error='0x08c379a0'+(32n).toString(16).padStart(64,'0')+(8n).toString(16).padStart(64,'0')+Buffer.from('combined').toString('hex').padEnd(64,'0');
const panic='0x4e487b71'+(0x32n).toString(16).padStart(64,'0');
export const vectors=[['readAll()',values('initial')],['fill()',values('fill')],['readAll()',values('fill')],['writeBool()',values('bool')],['readAll()',values('bool')],['shrinkOne()',values('one')],['readAll()',values('one')],['zero()',values('zero')],['readAll()',values('zero')],['regrow()',values('regrow')],['readAll()',values('regrow')],['writeSigned()',values('signed')],['readAll()',values('signed')],['writeMembers()',values('members')],['readAll()',values('members')],['dirtyGrow()',values('dirty')],['readAll()',values('dirty')],['restore()',values('members')],['failAfterWrite()',[],error],['readAll()',values('members')],['outOfBounds()',[],panic],['staticProbe()',['0']],['readAll()',values('members')],['readTyped()',[(0xa1b2c3n<<232n).toString(),String((1n<<160n)-1n),'1',String(word(-32768))]]]
 .map(([signature,expected,revertData])=>({signature,args:[],failure:!!revertData,revertData:revertData??'0x',expected:!revertData&&!['staticProbe()','readTyped()'].includes(signature)?['32','52',...expected]:expected}));
function layout(v){
 assert.deepEqual(v.storageLayout.storage.map(x=>[x.label,x.slot,x.offset,v.storageLayout.types[x.type].numberOfBytes]),[['ss','0',0,'32'],['us','1',0,'32'],['ws','2',0,'32'],['bs','3',0,'32'],['ys','4',0,'32'],['zs','5',0,'32'],['marker','6',0,'32']]);
 for(const [i,label,width] of [[0,'int16','2'],[1,'uint24','3'],[2,'uint256','32'],[3,'bool','1'],[4,'bytes3','3'],[5,'address','20']]){const t=v.storageLayout.types[v.storageLayout.storage[i].type];assert.equal(t.encoding,'dynamic_array');assert.equal(v.storageLayout.types[t.base].label,label);assert.equal(v.storageLayout.types[t.base].numberOfBytes,width);}
 assert.deepEqual(v.transientStorageLayout.storage,[]);
}
export function assertPrimitiveDynamicVariant(v){
 assert.equal(v.status,'working');assert.equal(v.initialGas,'100000000');assert.equal(v.stepLimit,5000000);
 for(const k of ['inputSha256','sourceSha256','creationSha256','runtimeSha256'])assert.match(v[k],/^[0-9a-f]{64}$/);
 assert.equal(v.sourceSha256,sha(readFileSync(new URL('./PrimitiveDynamic.sol',import.meta.url))));
 assert.ok(Number.isSafeInteger(v.runtimeCodeBytes)&&v.runtimeCodeBytes>0);assert.deepEqual(v.methodIdentifiers,selectors);layout(v);
 assert.deepEqual(v.hashInputs,[0n,1n,2n,3n,4n,5n].map(n=>n.toString(16).padStart(64,'0')));assert.deepEqual(v.dataRoots,H.map(String));
 assert.deepEqual(v.vectors,vectors);assert.deepEqual(v.encodedCalls,vectors.map(x=>'0x'+selectors[x.signature]));assert.equal(v.observed.length,24);
 assert.equal(v.deployment.failed,false);assert.equal(v.deployment.exception,null);assert.equal(v.deployment.returnData,'0x');assert.equal(v.deployment.runtimeCodeSha256,v.runtimeSha256);assert.equal(v.deployment.runtimeCodeBytes,v.runtimeCodeBytes);
 assert.ok(v.deployment.steps>0&&v.deployment.steps<=STEP_LIMIT);assert.ok(BigInt(v.deployment.gasUsed)>=0n&&BigInt(v.deployment.gasUsed)<=INITIAL_GAS);
 for(let i=0;i<vectors.length;i++){const a=v.observed[i],x=vectors[i];assert.equal(a.signature,x.signature);assert.equal(a.calldata,v.encodedCalls[i]);assert.equal(a.failed,x.failure);assert.equal(a.exception,x.failure?'revert':null);assert.deepEqual(a.values,x.expected);assert.equal(a.returnData,x.failure?x.revertData:abi(x.expected));assert.ok(a.steps>0&&a.steps<=STEP_LIMIT);assert.ok(BigInt(a.gasUsed)>=0n&&BigInt(a.gasUsed)<=INITIAL_GAS);}
}
export function assertPrimitiveDynamicReport(r){assert.equal(r.status,'working');assert.deepEqual(r.variants.map(x=>x.viaIR),[false,true]);r.variants.forEach(assertPrimitiveDynamicVariant);}
export async function replayPrimitiveDynamic(compile,onVariant=()=>{}){
 const source=readFileSync(new URL('./PrimitiveDynamic.sol',import.meta.url),'utf8'),variants=[];
 for(const viaIR of [false,true]){
  const input={language:'Solidity',sources:{'PrimitiveDynamic.sol':{content:source}},settings:{viaIR,evmVersion:'osaka',optimizer:{enabled:false,runs:200},metadata:{appendCBOR:false},outputSelection:{'*':{'':['ast'],'*':['abi','evm.bytecode.object','evm.deployedBytecode.object','evm.methodIdentifiers','storageLayout','transientStorageLayout']}}}};
  const output=compile(input),errors=(output.errors??[]).filter(x=>x.severity==='error');if(errors.length){variants.push({viaIR,status:'blocked',errors});continue;}
  const a=output.contracts['PrimitiveDynamic.sol'].PrimitiveDynamic,vm=await machine(STEP_LIMIT),observed=[];
  const made=await vm.call({data:Uint8Array.from(Buffer.from(a.evm.bytecode.object,'hex'))}),deployment=creationObservation(made.result.execResult,'constructor',made.metrics);assert.ok(made.result.createdAddress);
  for(const x of vectors){const calldata='0x'+a.evm.methodIdentifiers[x.signature],receipt=await vm.call({to:made.result.createdAddress,data:Uint8Array.from(Buffer.from(calldata.slice(2),'hex'))});observed.push({...observation(receipt.result.execResult,x.signature,receipt.metrics),calldata});}
  const v={viaIR,status:'working',inputSha256:sha(JSON.stringify(input)),sourceSha256:sha(source),creationSha256:sha(Buffer.from(a.evm.bytecode.object,'hex')),runtimeSha256:sha(Buffer.from(a.evm.deployedBytecode.object,'hex')),runtimeCodeBytes:a.evm.deployedBytecode.object.length/2,storageLayout:a.storageLayout,transientStorageLayout:a.transientStorageLayout,hashInputs:[0,1,2,3,4,5].map(n=>BigInt(n).toString(16).padStart(64,'0')),dataRoots:H.map(String),methodIdentifiers:a.evm.methodIdentifiers,encodedCalls:vectors.map(x=>'0x'+a.evm.methodIdentifiers[x.signature]),initialGas:INITIAL_GAS.toString(),stepLimit:STEP_LIMIT,vectors,deployment,observed};onVariant(v);assertPrimitiveDynamicVariant(v);variants.push(v);
 }
 const r={status:variants.every(x=>x.status==='working')?'working':'blocked',kind:'external-reference-only',boundary:'Finite mixed integer/scalar primitive storage, cross-family writes, raw dirty bool growth, alias/padding/rollback and ABI observations; no kernel/source/compiler or allocation adequacy.',variants};if(r.status==='working')assertPrimitiveDynamicReport(r);return r;
}
