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
const signatures=['copyThree(uint256,bool)'];
const selectors=Object.fromEntries(signatures.map(s=>[s,hex(keccak_256(Buffer.from(s))).slice(0,8)]));
const word=s=>BigInt('0x'+s).toString();
const encoded=x=>'0x'+selectors[x.signature]+abi(x.args).slice(2)+'dead77';
const vector=(source,empty,failure=false)=>{
 const x={signature:signatures[0],args:[String(source),String(empty)],storage:['0'],failure};
 const input=Buffer.from(encoded(x).slice(2),'hex');
 const copy=Buffer.from(Array.from({length:empty?0:3},(_,i)=>{const pos=BigInt(source)+BigInt(i);return pos<BigInt(input.length)?input[Number(pos)]:0;}));
 const raw='112233'+hex(copy)+'a5'.repeat(29-copy.length),payload=word('112233'.padEnd(64,'0'));
 x.expected=failure?[]:[224,288,word(raw),word(hex(keccak_256(copy))),input.length,1,1,3,payload,3,payload].map(String);
 x.returnData=failure?'0x':abi(x.expected);return x;
};
export const vectors=[vector(68,0),vector(69,0),vector(70,0),vector(71,0),vector(W-1n,0),vector(0,0),vector(W-1n,1),vector(68,2,true)];
const inputFor=(viaIR,source)=> ({language:'Solidity',sources:{'FrameCalldata.sol':{content:source}},settings:{viaIR,evmVersion:'osaka',optimizer:{enabled:false,runs:200},metadata:{appendCBOR:false},outputSelection:{'*':{'':['ast'],'*':['abi','evm.bytecode.object','evm.deployedBytecode.object','evm.methodIdentifiers','storageLayout','transientStorageLayout','ir','irOptimized']}}}});
export function assertFrameCalldataVariant(v){
 assert.equal(v.status,'working');assert.equal(v.initialGas,'100000000');assert.equal(v.stepLimit,5000000);
 for(const k of ['inputSha256','sourceSha256','creationSha256','runtimeSha256'])assert.match(v[k],/^[0-9a-f]{64}$/);
 const source=readFileSync(new URL('./FrameCalldata.sol',import.meta.url),'utf8');assert.equal(v.sourceSha256,sha(source));
 assert.equal(v.inputSha256,sha(JSON.stringify(inputFor(v.viaIR,source))));
 assert.ok(Number.isSafeInteger(v.runtimeCodeBytes)&&v.runtimeCodeBytes>0);
 assert.deepEqual(v.methodIdentifiers,selectors);assert.deepEqual(v.vectors,vectors);assert.deepEqual(v.encodedCalls,vectors.map(encoded));
 assert.deepEqual(v.storageLayout.storage.map(x=>[x.label,x.slot,x.offset]),[]);assert.deepEqual(v.transientStorageLayout.storage,[]);
 assert.equal(v.deployment.failed,false);assert.equal(v.deployment.exception,null);assert.equal(v.deployment.returnData,'0x');
 assert.equal(v.deployment.runtimeCodeSha256,v.runtimeSha256);assert.equal(v.deployment.runtimeCodeBytes,v.runtimeCodeBytes);
 assert.ok(v.deployment.steps>0&&v.deployment.steps<=STEP_LIMIT);assert.ok(BigInt(v.deployment.gasUsed)>=0n&&BigInt(v.deployment.gasUsed)<=INITIAL_GAS);
 assert.equal(v.observed.length,vectors.length);
 for(let i=0;i<vectors.length;i++){
  const x=vectors[i],z=v.observed[i];assert.equal(z.signature,x.signature);assert.equal(z.calldata,v.encodedCalls[i]);
  assert.equal(z.failed,x.failure);assert.equal(z.exception,x.failure?'revert':null);assert.deepEqual(z.values,x.expected);assert.equal(z.returnData,x.returnData);
  assert.deepEqual(z.storage,x.storage);assert.deepEqual(z.logs,[]);assert.ok(z.steps>0&&z.steps<=STEP_LIMIT);
  assert.ok(Number.isSafeInteger(z.maxStack)&&z.maxStack>=0&&z.maxStack<=1024);assert.ok(BigInt(z.gasUsed)>=0n&&BigInt(z.gasUsed)<=INITIAL_GAS);
 }
}
export function assertFrameCalldataReport(r){assert.equal(r.status,'working');assert.deepEqual(r.variants.map(v=>v.viaIR),[false,true]);r.variants.forEach(assertFrameCalldataVariant);}
export async function replayFrameCalldata(compile,onVariant=()=>{}){
 const source=readFileSync(new URL('./FrameCalldata.sol',import.meta.url),'utf8'),variants=[];
 for(const viaIR of [false,true]){
  const input=inputFor(viaIR,source);
  const output=compile(input),errors=(output.errors??[]).filter(x=>x.severity==='error');if(errors.length){variants.push({viaIR,status:'blocked',errors});onVariant(variants.at(-1));continue;}
  const artifact=output.contracts['FrameCalldata.sol'].FrameCalldata,vm=await machine(STEP_LIMIT),observed=[];
  const made=await vm.call({data:Uint8Array.from(Buffer.from(artifact.evm.bytecode.object,'hex'))}),deployment=creationObservation(made.result.execResult,'constructor',made.metrics);assert.ok(made.result.createdAddress);
  for(const x of vectors){const calldata=encoded(x),receipt=await vm.call({to:made.result.createdAddress,data:Uint8Array.from(Buffer.from(calldata.slice(2),'hex'))});const stored=await vm.evm.stateManager.getStorage(made.result.createdAddress,Buffer.alloc(32));observed.push({...observation(receipt.result.execResult,x.signature,receipt.metrics),calldata,storage:[stored.length?BigInt('0x'+hex(stored)).toString():'0'],logs:(receipt.result.execResult.logs??[]).map(([a,t,b])=>[hex(a),t.map(hex),hex(b)])});}
  const v={viaIR,status:'working',inputSha256:sha(JSON.stringify(input)),sourceSha256:sha(source),creationSha256:sha(Buffer.from(artifact.evm.bytecode.object,'hex')),runtimeSha256:sha(Buffer.from(artifact.evm.deployedBytecode.object,'hex')),runtimeCodeBytes:artifact.evm.deployedBytecode.object.length/2,storageLayout:artifact.storageLayout,transientStorageLayout:artifact.transientStorageLayout,methodIdentifiers:artifact.evm.methodIdentifiers,encodedCalls:vectors.map(encoded),initialGas:INITIAL_GAS.toString(),stepLimit:STEP_LIMIT,vectors,deployment,observed,ir:artifact.ir,irOptimized:artifact.irOptimized};onVariant(v);assertFrameCalldataVariant(v);variants.push(v);
 }
 const report={status:variants.every(v=>v.status==='working')?'working':'blocked',kind:'external-reference-only',boundary:'Finite exact whole-frame calldata/selector bytes, partial padding, maximum nonwrapping source, zero copy, actual keccak of copied bytes, reserved/free words and aliases; malformed bool input fails before body. Not frontend admission, seeded kernel equality, arbitrary memory safety or source/compiler/target adequacy.',variants};if(report.status==='working')assertFrameCalldataReport(report);return report;
}
