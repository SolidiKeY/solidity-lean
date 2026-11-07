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
const signatures=['readState()','readMap(uint256)','setMap(uint256,uint256,bool)','sameMap(uint256)','staticMap(uint256)','seed()','childTransient(bool)','transientScenario(bool,bool)','readTransient()','staticProbe()'];
const selectors=Object.fromEntries(signatures.map(s=>[s,hex(keccak_256(Buffer.from(s))).slice(0,8)]));
const hashSlot=k=>BigInt('0x'+hex(keccak_256(Buffer.from(abi([k,0]).slice(2),'hex')))).toString();
const splitWords=s=>{const raw=s.slice(2),padded=raw.padEnd(Math.ceil(raw.length/64)*64,'0');return Array.from({length:padded.length/64},(_,i)=>BigInt('0x'+padded.slice(i*64,i*64+64)).toString());};
const scenario=(childFails,count)=>{const data=childFails?reason('transient child'):abi([0xabcd,0xb6b6abcd,88]);return [0x1234,childFails?0x1234:0xabcd,childFails?0xa5a51234:0xb6b6abcd,childFails?77:88,childFails?0:1,224,count,(data.length-2)/2,...splitWords(data)].map(String);};
const vector=(signature,args,expected,marker,root=0,failure=false,returnData=null)=>({signature,args,expected:expected.map(String),storage:[String(root),String(marker)],failure,returnData:returnData??abi(expected)});
const read=(marker,root,x,y)=>vector('readState()',[],[marker,root,x,y],marker,root);
export const vectors=[read(0,0,0,0),vector('readMap(uint256)',[1],[0,0,hashSlot(1)],0),
 vector('setMap(uint256,uint256,bool)',[1,0,0],[0,0,hashSlot(1),1],1),
 vector('setMap(uint256,uint256,bool)',[2,999,0],[999,999,hashSlot(2),2],2),read(2,0,0,999),
 vector('setMap(uint256,uint256,bool)',[1,77,0],[77,77,hashSlot(1),3],3),
 vector('setMap(uint256,uint256,bool)',[2,888,1],[],3,0,true,reason('mapping')),read(3,0,77,999),
 vector('seed()',[],[777],3,777),
 vector('transientScenario(bool,bool)',[0,0],scenario(false,4),4,777),vector('readTransient()',[],[0,0,0],4,777),
 vector('transientScenario(bool,bool)',[1,0],scenario(true,5),5,777),vector('readTransient()',[],[0,0,0],5,777),
 vector('transientScenario(bool,bool)',[0,1],[],5,777,true,reason('transient outer')),read(5,777,77,999),
 vector('staticProbe()',[],[0,64,0],5,777),vector('readTransient()',[],[0,0,0],5,777),
 vector('transientScenario(bool,bool)',[0,0],scenario(false,6),6,777),read(6,777,77,999),
 vector('staticMap(uint256)',[1],[0,64,0],6,777),read(6,777,77,999),
 vector('readMap(uint256)',[1],[77,77,hashSlot(1)],6,777),vector('sameMap(uint256)',[1],[77],6,777)];
const mapStates=[[0,0],[0,0],[0,0],[0,999],[0,999],...Array.from({length:18},()=>[77,999])];assert.equal(mapStates.length,vectors.length);vectors.forEach((v,i)=>v.storage.push(...mapStates[i].map(String)));
const encoded=x=>'0x'+selectors[x.signature]+abi(x.args).slice(2);
const inputFor=(viaIR,source)=> ({language:'Solidity',sources:{'MappingTransient.sol':{content:source}},settings:{viaIR,evmVersion:'osaka',optimizer:{enabled:false,runs:200},metadata:{appendCBOR:false},outputSelection:{'*':{'':['ast'],'*':['abi','evm.bytecode.object','evm.deployedBytecode.object','evm.methodIdentifiers','storageLayout','transientStorageLayout','ir','irOptimized']}}}});
export function assertMappingTransientVariant(v){
 assert.equal(v.status,'working');assert.equal(v.initialGas,'100000000');assert.equal(v.stepLimit,5000000);
 for(const k of ['inputSha256','sourceSha256','creationSha256','runtimeSha256'])assert.match(v[k],/^[0-9a-f]{64}$/);
 const source=readFileSync(new URL('./MappingTransient.sol',import.meta.url),'utf8');assert.equal(v.sourceSha256,sha(source));
 assert.equal(v.inputSha256,sha(JSON.stringify(inputFor(v.viaIR,source))));
 assert.ok(Number.isSafeInteger(v.runtimeCodeBytes)&&v.runtimeCodeBytes>0);
 assert.deepEqual(v.methodIdentifiers,selectors);assert.deepEqual(v.vectors,vectors);assert.deepEqual(v.encodedCalls,vectors.map(encoded));
 assert.deepEqual(v.storageLayout.storage.map(x=>[x.label,x.slot,x.offset]),[['table','0',0],['marker','1',0]]);assert.deepEqual(v.transientStorageLayout.storage.map(x=>[x.label,x.slot,x.offset]),[['temp','0',0]]);
 assert.equal(v.deployment.failed,false);assert.equal(v.deployment.exception,null);assert.equal(v.deployment.returnData,'0x');
 assert.equal(v.deployment.runtimeCodeSha256,v.runtimeSha256);assert.equal(v.deployment.runtimeCodeBytes,v.runtimeCodeBytes);
 assert.ok(v.deployment.steps>0&&v.deployment.steps<=STEP_LIMIT);assert.ok(BigInt(v.deployment.gasUsed)>=0n&&BigInt(v.deployment.gasUsed)<=INITIAL_GAS);
 assert.equal(v.observed.length,vectors.length);
 for(let i=0;i<vectors.length;i++){
  const x=vectors[i],z=v.observed[i];assert.equal(z.signature,x.signature);assert.equal(z.calldata,v.encodedCalls[i]);
  assert.equal(z.failed,x.failure);assert.equal(z.exception,x.failure?'revert':null);assert.deepEqual(z.values,x.expected);assert.equal(z.returnData,x.returnData);
  assert.deepEqual(z.storage,x.storage);assert.deepEqual(z.transientAfter,['0','0']);assert.deepEqual(z.logs,[]);assert.ok(z.steps>0&&z.steps<=STEP_LIMIT);
  assert.ok(Number.isSafeInteger(z.maxStack)&&z.maxStack>=0&&z.maxStack<=1024);assert.ok(BigInt(z.gasUsed)>=0n&&BigInt(z.gasUsed)<=INITIAL_GAS);
 }
}
export function assertMappingTransientReport(r){assert.equal(r.status,'working');assert.deepEqual(r.variants.map(v=>v.viaIR),[false,true]);r.variants.forEach(assertMappingTransientVariant);}
export async function replayMappingTransient(compile,onVariant=()=>{}){
 const source=readFileSync(new URL('./MappingTransient.sol',import.meta.url),'utf8'),variants=[];
 for(const viaIR of [false,true]){
  const input=inputFor(viaIR,source);
  const output=compile(input),errors=(output.errors??[]).filter(x=>x.severity==='error');if(errors.length){variants.push({viaIR,status:'blocked',errors});onVariant(variants.at(-1));continue;}
  const artifact=output.contracts['MappingTransient.sol'].MappingTransient,vm=await machine(STEP_LIMIT),observed=[];
  const made=await vm.call({data:Uint8Array.from(Buffer.from(artifact.evm.bytecode.object,'hex'))}),deployment=creationObservation(made.result.execResult,'constructor',made.metrics);assert.ok(made.result.createdAddress);
  for(const x of vectors){const calldata=encoded(x),receipt=await vm.call({to:made.result.createdAddress,data:Uint8Array.from(Buffer.from(calldata.slice(2),'hex'))});const stored=[];for(const slot of [0,1,hashSlot(1),hashSlot(2)]){const key=Buffer.from(BigInt(slot).toString(16).padStart(64,'0'),'hex');const bytes=await vm.evm.stateManager.getStorage(made.result.createdAddress,key);stored.push(bytes.length?BigInt('0x'+hex(bytes)).toString():'0');}observed.push({...observation(receipt.result.execResult,x.signature,receipt.metrics),calldata,storage:stored,transientAfter:[0,99].map(slot=>{const key=Buffer.alloc(32);key[31]=slot;const bytes=vm.evm.transientStorage.get(made.result.createdAddress,key);return bytes.length?BigInt('0x'+hex(bytes)).toString():'0';}),logs:(receipt.result.execResult.logs??[]).map(([a,t,b])=>[hex(a),t.map(hex),hex(b)])});}
  const v={viaIR,status:'working',inputSha256:sha(JSON.stringify(input)),sourceSha256:sha(source),creationSha256:sha(Buffer.from(artifact.evm.bytecode.object,'hex')),runtimeSha256:sha(Buffer.from(artifact.evm.deployedBytecode.object,'hex')),runtimeCodeBytes:artifact.evm.deployedBytecode.object.length/2,storageLayout:artifact.storageLayout,transientStorageLayout:artifact.transientStorageLayout,methodIdentifiers:artifact.evm.methodIdentifiers,encodedCalls:vectors.map(encoded),initialGas:INITIAL_GAS.toString(),stepLimit:STEP_LIMIT,vectors,deployment,observed,ir:artifact.ir,irOptimized:artifact.irOptimized};onVariant(v);assertMappingTransientVariant(v);variants.push(v);
 }
 const report={status:variants.every(v=>v.status==='working')?'working':'blocked',kind:'external-reference-only',boundary:'Finite mapping exact-keccak slot/raw/typed reads and unchanged SSTORE, actual transient typed/residual/unknown slots, child rollback and outer rollback/static/fresh-transaction reset with persistent bank preservation. Not frontend admission, seeded kernel equality, arbitrary memory safety or source/compiler/target adequacy.',variants};if(report.status==='working')assertMappingTransientReport(report);return report;
}
