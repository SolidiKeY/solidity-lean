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
const signatures=['readState()','run(uint256,bool)','staticProbe()'];
const selectors=Object.fromEntries(signatures.map(s=>[s,hex(keccak_256(Buffer.from(s))).slice(0,8)]));
const word=s=>BigInt('0x'+s).toString();
const output=mode=>[160,224,word((mode===1?'11223311112233':mode===2?'11223311223333':'112233112233')+'a5'.repeat(mode===1||mode===2?25:26)),1,1,3,word('112233'.padEnd(64,'0')),3,word('112233'.padEnd(64,'0'))].map(String);
const vector=(signature,args,expected,marker,failure=false,returnData=null)=>({signature,args,expected:expected.map(String),storage:[String(marker)],failure,returnData:returnData??abi(expected)});
const read=n=>vector('readState()',[],[n],n);
export const vectors=[read(0),vector('run(uint256,bool)',[0,0],output(0),1),vector('run(uint256,bool)',[1,0],output(1),2),
 vector('run(uint256,bool)',[2,0],output(2),3),read(3),vector('run(uint256,bool)',[3,0],output(3),4),
 vector('run(uint256,bool)',[2,1],[],4,true,reason('copies')),read(4),vector('staticProbe()',[],[0,64,0],4),read(4),
 vector('run(uint256,bool)',[1,0],output(1),5),read(5)];
const encoded=x=>'0x'+selectors[x.signature]+abi(x.args).slice(2);
const inputFor=(viaIR,source)=> ({language:'Solidity',sources:{'ResidualMcopy.sol':{content:source}},settings:{viaIR,evmVersion:'osaka',optimizer:{enabled:false,runs:200},metadata:{appendCBOR:false},outputSelection:{'*':{'':['ast'],'*':['abi','evm.bytecode.object','evm.deployedBytecode.object','evm.methodIdentifiers','storageLayout','transientStorageLayout','ir','irOptimized']}}}});
export function assertResidualMcopyVariant(v){
 assert.equal(v.status,'working');assert.equal(v.initialGas,'100000000');assert.equal(v.stepLimit,5000000);
 for(const k of ['inputSha256','sourceSha256','creationSha256','runtimeSha256'])assert.match(v[k],/^[0-9a-f]{64}$/);
 const source=readFileSync(new URL('./ResidualMcopy.sol',import.meta.url),'utf8');assert.equal(v.sourceSha256,sha(source));
 assert.equal(v.inputSha256,sha(JSON.stringify(inputFor(v.viaIR,source))));
 assert.ok(Number.isSafeInteger(v.runtimeCodeBytes)&&v.runtimeCodeBytes>0);
 assert.deepEqual(v.methodIdentifiers,selectors);assert.deepEqual(v.vectors,vectors);assert.deepEqual(v.encodedCalls,vectors.map(encoded));
 assert.deepEqual(v.storageLayout.storage.map(x=>[x.label,x.slot,x.offset]),[['marker','0',0]]);assert.deepEqual(v.transientStorageLayout.storage,[]);
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
export function assertResidualMcopyReport(r){assert.equal(r.status,'working');assert.deepEqual(r.variants.map(v=>v.viaIR),[false,true]);r.variants.forEach(assertResidualMcopyVariant);}
export async function replayResidualMcopy(compile,onVariant=()=>{}){
 const source=readFileSync(new URL('./ResidualMcopy.sol',import.meta.url),'utf8'),variants=[];
 for(const viaIR of [false,true]){
  const input=inputFor(viaIR,source);
  const output=compile(input),errors=(output.errors??[]).filter(x=>x.severity==='error');if(errors.length){variants.push({viaIR,status:'blocked',errors});onVariant(variants.at(-1));continue;}
  const artifact=output.contracts['ResidualMcopy.sol'].ResidualMcopy,vm=await machine(STEP_LIMIT),observed=[];
  const made=await vm.call({data:Uint8Array.from(Buffer.from(artifact.evm.bytecode.object,'hex'))}),deployment=creationObservation(made.result.execResult,'constructor',made.metrics);assert.ok(made.result.createdAddress);
  for(const x of vectors){const calldata=encoded(x),receipt=await vm.call({to:made.result.createdAddress,data:Uint8Array.from(Buffer.from(calldata.slice(2),'hex'))});const stored=await vm.evm.stateManager.getStorage(made.result.createdAddress,Buffer.alloc(32));observed.push({...observation(receipt.result.execResult,x.signature,receipt.metrics),calldata,storage:[stored.length?BigInt('0x'+hex(stored)).toString():'0'],logs:(receipt.result.execResult.logs??[]).map(([a,t,b])=>[hex(a),t.map(hex),hex(b)])});}
  const v={viaIR,status:'working',inputSha256:sha(JSON.stringify(input)),sourceSha256:sha(source),creationSha256:sha(Buffer.from(artifact.evm.bytecode.object,'hex')),runtimeSha256:sha(Buffer.from(artifact.evm.deployedBytecode.object,'hex')),runtimeCodeBytes:artifact.evm.deployedBytecode.object.length/2,storageLayout:artifact.storageLayout,transientStorageLayout:artifact.transientStorageLayout,methodIdentifiers:artifact.evm.methodIdentifiers,encodedCalls:vectors.map(encoded),initialGas:INITIAL_GAS.toString(),stepLimit:STEP_LIMIT,vectors,deployment,observed,ir:artifact.ir,irOptimized:artifact.irOptimized};onVariant(v);assertResidualMcopyVariant(v);variants.push(v);
 }
 const report={status:variants.every(v=>v.status==='working')?'working':'blocked',kind:'external-reference-only',boundary:'Finite chronological overlapping mcopy snapshot/order/padding/alias/full ABI, exact revert/static/storage rollback, zero-size high-source and reserved/free-word observations. Not frontend admission, seeded kernel equality, arbitrary memory safety or source/compiler/target adequacy.',variants};if(report.status==='working')assertResidualMcopyReport(report);return report;
}
