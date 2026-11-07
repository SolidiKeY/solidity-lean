// Finite external controls only; not source/compiler or whole-store adequacy.
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {createRequire} from 'node:module';
const {keccak_256}=await import(createRequire(new URL('../../scripts/evm-reference/replay.mjs',import.meta.url)).resolve('@noble/hashes/sha3.js'));
import {machine,observation,creationObservation,INITIAL_GAS,STEP_LIMIT} from '../../scripts/evm-reference/replay.mjs';
const sha=x=>createHash('sha256').update(x).digest('hex');
const hex=x=>Buffer.from(x).toString('hex');
const abi=xs=>'0x'+xs.map(x=>BigInt(x).toString(16).padStart(64,'0')).join('');
const hashWord=n=>BigInt('0x'+hex(keccak_256(Buffer.from(BigInt(n).toString(16).padStart(64,'0'),'hex'))));
const HX=hashWord(43),HY=hashWord(45),MAX=(1n<<256n)-1n,PAD=BigInt('0x'+'cc'.repeat(30)+'0000'),TPAD=BigInt('0x'+'dd'.repeat(30)+'0000');
assert.ok(HX+8n<(1n<<256n)&&HY+8n<(1n<<256n));
assert.ok(HX>HY?HX-HY>=8n:HY-HX>=8n);
for(const h of [HX,HY])for(const r of [42n,43n,44n,45n,46n])assert.ok(r<h||r>=h+8n);
const names=['readAll()','fill()','shrink()','regrow()','failAfterWrite()','outOfBounds()','staticProbe()'];
const selectors=Object.fromEntries(names.map(x=>[x,hex(keccak_256(Buffer.from(x))).slice(0,8)]));
function values(stage,temp=false){
 const written=stage!=='initial',zero=stage==='initial'||stage==='shrink',nx=zero?0:stage==='regrow'?3:2,ny=zero?0:1;
 return [nx,nx,ny,nx?12:0,nx>1?MAX:0,ny?33:0,55,written?0x1234:0,temp?0x7788:0,
 written?MAX-238n:0,nx,PAD+(written?0x1234n:0n),ny,55,999,HX,HY,written?12:0,written?MAX:0,written?77:0,written?33:0,temp?TPAD+0x7788n:0n].map(String);
}
const error=text=>'0x08c379a0'+(32n).toString(16).padStart(64,'0')+BigInt(text.length).toString(16).padStart(64,'0')+Buffer.from(text).toString('hex').padEnd(64,'0');
const panic='0x4e487b71'+(0x32n).toString(16).padStart(64,'0');
export const vectors=[
 ['readAll()',values('initial')],['fill()',values('fill',true)],['readAll()',values('fill')],
 ['shrink()',values('shrink')],['readAll()',values('shrink')],['regrow()',values('regrow')],
 ['readAll()',values('regrow')],['failAfterWrite()',[],error('dynamic')],['readAll()',values('regrow')],
 ['outOfBounds()',[],panic],['staticProbe()',['0']],['readAll()',values('regrow')]
].map(([signature,expected,revertData])=>({signature,args:[],failure:!!revertData,revertData:revertData??'0x',expected}));
function layout(l,t){
 assert.deepEqual(l.storage.map(x=>[x.label,x.slot,x.offset,l.types[x.type].numberOfBytes]),[['a','42',0,'1'],['n','42',1,'31'],['xs','43',0,'32'],['mid','44',0,'2'],['ys','45',0,'32'],['marker','46',0,'32']]);
 for(const i of [2,4]){const a=l.types[l.storage[i].type];assert.equal(a.encoding,'dynamic_array');assert.equal(l.types[a.base].label,'uint256');assert.equal(l.types[a.base].numberOfBytes,'32');}
 assert.deepEqual(t.storage.map(x=>[x.label,x.slot,x.offset,t.types[x.type].numberOfBytes]),[['temp','0',0,'2']]);
}
export function assertDynamicStorageVariant(v){
 assert.equal(v.status,'working');assert.equal(v.initialGas,'100000000');assert.equal(v.stepLimit,5000000);
 for(const k of ['inputSha256','sourceSha256','creationSha256','runtimeSha256'])assert.match(v[k],/^[0-9a-f]{64}$/);
 assert.equal(v.sourceSha256,sha(readFileSync(new URL('./DynamicStorage.sol',import.meta.url))));assert.ok(Number.isSafeInteger(v.runtimeCodeBytes)&&v.runtimeCodeBytes>0);
 assert.deepEqual(v.methodIdentifiers,selectors);layout(v.storageLayout,v.transientStorageLayout);
 assert.deepEqual(v.lineage,['DynamicStorage','DynamicBase']);assert.deepEqual(v.sourceOwners,[['DynamicBase','a'],['DynamicStorage','n'],['DynamicStorage','xs'],['DynamicStorage','mid'],['DynamicStorage','ys'],['DynamicStorage','marker']]);
 assert.deepEqual(v.hashInputs,[(43n).toString(16).padStart(64,'0'),(45n).toString(16).padStart(64,'0')]);assert.deepEqual(v.dataRoots,[String(HX),String(HY)]);
 assert.deepEqual(v.vectors,vectors);assert.deepEqual(v.encodedCalls,vectors.map(x=>'0x'+selectors[x.signature]));assert.equal(v.observed.length,vectors.length);
 assert.equal(v.deployment.failed,false);assert.equal(v.deployment.exception,null);assert.equal(v.deployment.returnData,'0x');assert.equal(v.deployment.runtimeCodeSha256,v.runtimeSha256);assert.equal(v.deployment.runtimeCodeBytes,v.runtimeCodeBytes);
 assert.ok(v.deployment.steps>0&&v.deployment.steps<=STEP_LIMIT);assert.ok(BigInt(v.deployment.gasUsed)>=0n&&BigInt(v.deployment.gasUsed)<=INITIAL_GAS);
 for(let i=0;i<vectors.length;i++){const a=v.observed[i],x=vectors[i];assert.equal(a.signature,x.signature);assert.equal(a.calldata,v.encodedCalls[i]);assert.equal(a.failed,x.failure);assert.equal(a.exception,x.failure?'revert':null);assert.deepEqual(a.values,x.expected);assert.equal(a.returnData,x.failure?x.revertData:abi(x.expected));assert.ok(a.steps>0&&a.steps<=STEP_LIMIT);assert.ok(BigInt(a.gasUsed)>=0n&&BigInt(a.gasUsed)<=INITIAL_GAS);}
}
export function assertDynamicStorageReport(r){assert.equal(r.status,'working');assert.deepEqual(r.variants.map(x=>x.viaIR),[false,true]);r.variants.forEach(assertDynamicStorageVariant);}
export async function replayDynamicStorage(compile,onVariant=()=>{}){
 const source=readFileSync(new URL('./DynamicStorage.sol',import.meta.url),'utf8'),variants=[];
 for(const viaIR of [false,true]){
  const input={language:'Solidity',sources:{'DynamicStorage.sol':{content:source}},settings:{viaIR,evmVersion:'osaka',optimizer:{enabled:false,runs:200},metadata:{appendCBOR:false},outputSelection:{'*':{'':['ast'],'*':['abi','evm.bytecode.object','evm.deployedBytecode.object','evm.methodIdentifiers','storageLayout','transientStorageLayout']}}}};
  const output=compile(input),errors=(output.errors??[]).filter(x=>x.severity==='error');if(errors.length){variants.push({viaIR,status:'blocked',errors});continue;}
  const ast=output.sources['DynamicStorage.sol'].ast,contracts=ast.nodes.filter(x=>x.nodeType==='ContractDefinition'),active=contracts.find(x=>x.name==='DynamicStorage'),ownership=Object.fromEntries(contracts.flatMap(c=>c.nodes.filter(n=>n.nodeType==='VariableDeclaration').map(n=>[n.id,c.name])));
  const a=output.contracts['DynamicStorage.sol'].DynamicStorage,vm=await machine(STEP_LIMIT),observed=[];
  const made=await vm.call({data:Uint8Array.from(Buffer.from(a.evm.bytecode.object,'hex'))}),deployment=creationObservation(made.result.execResult,'constructor',made.metrics);assert.ok(made.result.createdAddress);
  for(const x of vectors){const calldata='0x'+a.evm.methodIdentifiers[x.signature],receipt=await vm.call({to:made.result.createdAddress,data:Uint8Array.from(Buffer.from(calldata.slice(2),'hex'))});observed.push({...observation(receipt.result.execResult,x.signature,receipt.metrics),calldata});}
  const v={viaIR,status:'working',inputSha256:sha(JSON.stringify(input)),sourceSha256:sha(source),creationSha256:sha(Buffer.from(a.evm.bytecode.object,'hex')),runtimeSha256:sha(Buffer.from(a.evm.deployedBytecode.object,'hex')),runtimeCodeBytes:a.evm.deployedBytecode.object.length/2,storageLayout:a.storageLayout,transientStorageLayout:a.transientStorageLayout,lineage:active.linearizedBaseContracts.map(id=>contracts.find(c=>c.id===id)?.name??null),sourceOwners:a.storageLayout.storage.map(x=>[ownership[x.astId],x.label]),hashInputs:[43,45].map(n=>BigInt(n).toString(16).padStart(64,'0')),dataRoots:[String(HX),String(HY)],methodIdentifiers:a.evm.methodIdentifiers,encodedCalls:vectors.map(x=>'0x'+a.evm.methodIdentifiers[x.signature]),initialGas:INITIAL_GAS.toString(),stepLimit:STEP_LIMIT,vectors,deployment,observed};onVariant(v);assertDynamicStorageVariant(v);variants.push(v);
 }
 const r={status:variants.every(x=>x.status==='working')?'working':'blocked',kind:'external-reference-only',boundary:'Finite inherited computed layout-at42 dynamic uint256 header/data/aliases/tails, transient0, static failure and rollback. Not universal dirty/source/compiler or allocation adequacy.',variants};if(r.status==='working')assertDynamicStorageReport(r);return r;
}
