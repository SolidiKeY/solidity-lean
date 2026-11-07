// Narrow VY2 complement/packed-slot vectors; unchanged public bounded EVM.
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {machine,observation,creationObservation,INITIAL_GAS,STEP_LIMIT} from '../../scripts/evm-reference/replay.mjs';
const sha=x=>createHash('sha256').update(x).digest('hex');
const selectors={'child(bool)':'08fc43c4','dirtyOwned()':'28b5dc78','forward()':'d264e05e','innerRevertPrefix()':'d1d80ace','orderForward()':'aec92f7c','orderReverse()':'d742ca58','outerRevertAfterChild()':'0999112d','readStored()':'24ba3473','staticAttempt()':'27a3a9bc','successAndTransient()':'26dfb5d5','typedChanges()':'9379ea80'};
// Independent slot arithmetic: bytes0 bool,1..2 uint16,3..5 bytes3,
// 6..25 address,26..31 arbitrary nonzero residual. ABI bytes3 is LEFT aligned.
const Z=BigInt('0x'+'a5'.repeat(6)+'00'.repeat(26));
const lowA=BigInt('0x1234567890123456789012345678901234567890')*256n**6n+0xff00aan*256n**3n+0x1234n*256n+1n;
const A=Z+lowA;
const B=BigInt('0x'+'5a'.repeat(6)+'00'.repeat(26))+BigInt('0xabcdefabcdefabcdefabcdefabcdefabcdefabcd')*256n**6n+0x112233n*256n**3n+0xbeefn*256n;
const C=(B>>208n<<208n)+lowA,D=A-1n+2n;
const fields=w=>[(w&255n)?1n:0n,(w>>8n)&65535n,((w>>24n)&0xffffffn)<<232n,(w>>48n)&((1n<<160n)-1n)];
const view=(s,t=0n)=>[s,t,...fields(s),...fields(t),55n,55n,0n].map(String);
const good=(signature,expected)=>({signature,args:[],failure:false,expected});
const vectors=[good('readStored()',view(Z)),good('forward()',view(A,A)),good('readStored()',view(A)),
 good('orderForward()',view(B,B)),good('orderReverse()',view(A,A)),good('innerRevertPrefix()',view(A,A)),good('readStored()',view(A)),
 {signature:'outerRevertAfterChild()',args:[],failure:true,expected:[]},good('readStored()',view(A)),
 good('successAndTransient()',view(B,B)),good('readStored()',view(B)),good('typedChanges()',view(C,lowA)),good('readStored()',view(C)),
 good('dirtyOwned()',view(D)),good('readStored()',view(D)),good('staticAttempt()',['0',String(D)]),
 {signature:'child(bool)',args:['0'],failure:true,expected:[]},good('readStored()',view(D))];
const calldata=v=>'0x'+selectors[v.signature]+v.args.map(x=>BigInt(x).toString(16).padStart(64,'0')).join('');
const abi=xs=>'0x'+xs.map(x=>BigInt(x).toString(16).padStart(64,'0')).join('');
function layouts(s,t){
 assert.deepEqual(s.storage.map(x=>[x.label,x.slot,x.offset]),[['flag','7',0],['small','7',1],['data','7',3],['who','7',6],['other','8',0]]);
 assert.deepEqual(s.storage.map(x=>s.types[x.type].numberOfBytes),['1','2','3','20','32']);
 assert.deepEqual(t.storage.map(x=>[x.label,x.slot,x.offset]),[...Array.from({length:7},(_,i)=>['t'+i,String(i),0]),['txFlag','7',0],['txSmall','7',1],['txData','7',3],['txWho','7',6]]);
 assert.deepEqual(t.storage.map(x=>t.types[x.type].numberOfBytes),[...Array(7).fill('32'),'1','2','3','20']);
}
export function assertPackedResidualVariant(v){
 for(const key of ['inputSha256','sourceSha256','creationSha256','runtimeSha256'])assert.match(v[key],/^[0-9a-f]{64}$/);
 assert.ok(Number.isSafeInteger(v.runtimeCodeBytes)&&v.runtimeCodeBytes>0);
 assert.equal(v.status,'working');assert.equal(v.initialGas,'100000000');assert.equal(v.stepLimit,5000000);
 assert.deepEqual(v.methodIdentifiers,selectors);layouts(v.storageLayout,v.transientStorageLayout);
 assert.equal(v.deployment?.failed,false);assert.equal(v.deployment.exception,null);assert.equal(v.deployment.returnData,'0x');
 assert.equal(v.deployment.runtimeCodeSha256,v.runtimeSha256);assert.equal(v.deployment.runtimeCodeBytes,v.runtimeCodeBytes);
 assert.deepEqual(v.vectors,vectors);assert.equal(v.observed.length,vectors.length);assert.deepEqual(v.encodedCalls,vectors.map(calldata));
 for(let i=0;i<vectors.length;i++){
  const e=vectors[i],a=v.observed[i];assert.equal(a.signature,e.signature);assert.equal(a.calldata,calldata(e));assert.equal(a.failed,e.failure);
  assert.equal(a.exception,e.failure?'revert':null);assert.deepEqual(a.values,e.expected);
  assert.equal(a.returnData,e.failure?'0x':abi(e.expected));
  assert.ok(a.steps>0&&a.steps<=STEP_LIMIT);assert.ok(BigInt(a.gasUsed)>=0n&&BigInt(a.gasUsed)<=INITIAL_GAS);
 }
 assert.ok(v.deployment.steps>0&&v.deployment.steps<=STEP_LIMIT);assert.ok(BigInt(v.deployment.gasUsed)<=INITIAL_GAS);
}
export function assertPackedResidualReport(r){assert.equal(r.status,'working');assert.equal(r.variants.length,2);assert.deepEqual(r.variants.map(x=>x.viaIR),[false,true]);r.variants.forEach(assertPackedResidualVariant);}
// Narrow adapter over public reference APIs: every receipt records the EXACT
// bytes passed to vm.call, with no shared replay or general harness changes.
async function replayPackedBytecode(a){
 const vm=await machine(STEP_LIMIT),observed=[];let deployment;
 try{
  const created=await vm.call({data:Uint8Array.from(Buffer.from(a.evm.bytecode.object,'hex'))});
  deployment=creationObservation(created.result.execResult,'constructor',created.metrics);
  if(deployment.failed||!created.result.createdAddress)return {status:'blocked',reason:'creation failed',deployment,observed};
  const address=created.result.createdAddress;
  for(const vector of vectors){
   const selector=a.evm.methodIdentifiers[vector.signature];
   if(!selector)throw Error('missing selector '+vector.signature);
   const bytes=Buffer.from(selector+vector.args.map(x=>BigInt(x).toString(16).padStart(64,'0')).join(''),'hex');
   const call=await vm.call({to:address,data:Uint8Array.from(bytes)});
   const actual={...observation(call.result.execResult,vector.signature,call.metrics),calldata:'0x'+bytes.toString('hex')};
   observed.push(actual);
   if(actual.failed!==vector.failure||JSON.stringify(actual.values)!==JSON.stringify(vector.expected)||actual.returnData!==(vector.failure?'0x':abi(vector.expected)))
    return {status:'broken',reason:'complete ordered observation mismatch',deployment,observed,expected:vector};
  }
  return {status:'working',deployment,observed};
 }catch(e){return {status:'blocked',reason:e.message,deployment,observed};}
}
export async function replayPackedResidual(compile){
 const source=readFileSync(new URL('./PackedResidual.sol',import.meta.url),'utf8'),variants=[];
 for(const viaIR of [false,true]){
  const input={language:'Solidity',sources:{'PackedResidual.sol':{content:source}},settings:{viaIR,evmVersion:'osaka',optimizer:{enabled:false,runs:200},metadata:{appendCBOR:false},outputSelection:{'*':{'*':['abi','evm.bytecode.object','evm.deployedBytecode.object','evm.methodIdentifiers','storageLayout','transientStorageLayout']}}}};
  const out=compile(input),errors=(out.errors??[]).filter(e=>e.severity==='error');
  if(errors.length){variants.push({viaIR,status:'blocked',errors});continue;}
  const a=out.contracts['PackedResidual.sol'].PackedResidual;layouts(a.storageLayout,a.transientStorageLayout);
  const v={viaIR,inputSha256:sha(JSON.stringify(input)),sourceSha256:sha(source),creationSha256:sha(Buffer.from(a.evm.bytecode.object,'hex')),runtimeSha256:sha(Buffer.from(a.evm.deployedBytecode.object,'hex')),runtimeCodeBytes:a.evm.deployedBytecode.object.length/2,
   storageLayout:a.storageLayout,transientStorageLayout:a.transientStorageLayout,methodIdentifiers:a.evm.methodIdentifiers,encodedCalls:vectors.map(calldata),initialGas:INITIAL_GAS.toString(),stepLimit:STEP_LIMIT,vectors,...await replayPackedBytecode(a)};
  if(v.status==='working')assertPackedResidualVariant(v);variants.push(v);
 }
 const r={kind:'external-reference-only',boundary:'Finite registered byte complements; complete raw slots, same-slot bank isolation, ordered rollback/reset and dirty bool observable. Administrative none/default identity is kernel-only. No whole-store/hash ownership, Yul admission or compiler correspondence claim.',variants,status:variants.every(v=>v.status==='working')?'working':variants.some(v=>v.status==='broken')?'broken':'blocked'};
 if(r.status==='working')assertPackedResidualReport(r);return r;
}
