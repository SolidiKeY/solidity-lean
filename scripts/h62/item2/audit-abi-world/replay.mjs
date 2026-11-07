// Bounded external reference tests only. No Lean gas/fork or world bridge proof.
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import {createHash} from 'node:crypto';
import {createRequire} from 'node:module';
import {fileURLToPath} from 'node:url';
const [vectorsFile,referenceRoot,provenanceFile]=process.argv.slice(2);assert(vectorsFile&&referenceRoot&&provenanceFile);
const sha=b=>createHash('sha256').update(b).digest('hex');
const lockBytes=fs.readFileSync(path.join(referenceRoot,'package-lock.json'));
assert.equal(sha(lockBytes),'fd223698b68dd5cf9dc1b59589c61da6c0131c3f68af65f7c26a3d5ac0498829');
const lock=JSON.parse(lockBytes);
const require=createRequire(path.join(path.resolve(referenceRoot),'reference.cjs'));
const {createEVM}=require('@ethereumjs/evm');
const {Common,Mainnet,Hardfork}=require('@ethereumjs/common');
assert(Hardfork.Osaka&&Hardfork.Homestead&&Hardfork.Byzantium);
const raw=fs.readFileSync(vectorsFile),vectors=JSON.parse(raw),W=1n<<256n;
const provenanceBytes=fs.readFileSync(provenanceFile),provenance=JSON.parse(provenanceBytes);
const root=path.resolve(path.dirname(fileURLToPath(import.meta.url)),'../../../..');
assert.equal(provenance.root,root);assert.equal(provenance.vectors_sha256,sha(raw));
assert.equal(provenance.source,path.join(root,'tests/h62/item2/audit-abi-world/H62AbiWorld/RuntimeVectors.lean'));
for(const [field,digest] of [['source','source_sha256'],['diagnostic','diagnostic_sha256'],['resource','resource_sha256']])
 assert.equal(sha(fs.readFileSync(provenance[field])),provenance[digest],`stale ${field}`);
assert.equal(sha(fs.readFileSync(path.join(root,'scripts/h62/item2/audit-abi-world/extract_vectors.py'))),provenance.extractor_sha256);
const localFolder=path.dirname(provenance.source);
assert.deepEqual(Object.keys(provenance.local_sources).sort(),fs.readdirSync(localFolder).filter(n=>n.endsWith('.lean')).map(n=>path.relative(root,path.join(localFolder,n))).sort());
for(const [relative,digest]of Object.entries({...provenance.local_sources,...provenance.support}))
 assert.equal(sha(fs.readFileSync(path.join(root,relative))),digest,`stale source/support ${relative}`);
const diagnostic=JSON.parse(fs.readFileSync(provenance.diagnostic));
const produced=diagnostic.structuredContent.result.items.filter(x=>x.message.startsWith('H62_VECTORS='));
assert.equal(produced.length,1);assert.deepEqual(vectors,JSON.parse(produced[0].message.slice(12)));

const word=n=>BigInt(n).toString(16).padStart(64,'0');
const hex=xs=>Buffer.from(xs).toString('hex');
const payloads=new Map([
 ['return_two','00ff'],['return_suffix','00ff'],['return_word300',word(300)],['empty_revert',''],
 ['panic300','4e487b71'+word(300)],
 ['error_two','08c379a0'+word(32)+word(2)+'00ff'+'00'.repeat(30)]]);
const adds=new Map([['add_small',[2n,3n]],['add_zero',[0n,0n]],['add_max_no_overflow',[W-1n,0n]],['add_overflow',[W-1n,1n]]]);
assert.equal(vectors.length,10);assert.equal(new Set(vectors.map(v=>v.name)).size,10);
assert.deepEqual(new Set(vectors.map(v=>v.name)),new Set([...payloads.keys(),...adds.keys()]));
async function observe(v,fork,gas){
 const evm=await createEVM({common:new Common({chain:Mainnet,hardfork:fork})});let steps=0;
 evm.events.on('step',()=>{if(++steps>100000)throw Error('HOST_STEP_BUDGET_EXHAUSTED');});
 const r=await evm.runCode({code:Uint8Array.from(v.code),gasLimit:gas});
 return {kind:r.exceptionError?.error??'success',data:hex(r.returnValue),gas:BigInt(r.executionGasUsed),steps,
   stack:r.runState.stack.getStack().map(String),memory:r.runState.memory};
}
function expected(v){
 if(v.program_kind==='packet')return {kind:v.name.startsWith('return_')?'success':'revert',data:payloads.get(v.name),stack:['77']};
 const [a,b]=adds.get(v.name);assert.equal(v.a,String(a));assert.equal(v.b,String(b));
 return a+b<W?{kind:'success',data:'',stack:[String(a+b)]}:{kind:'revert',data:'4e487b71'+word(17),stack:[String(a),String(b)]};
}
function agrees(r,e){return r.kind===e.kind&&r.data===e.data&&JSON.stringify(r.stack)===JSON.stringify(e.stack);}
const rows=[];
for(const v of vectors){
 assert.equal(v.compiled,true);assert(v.code.every(n=>Number.isInteger(n)&&0<=n&&n<=255));
 if(v.program_kind==='packet'){
  assert.equal(hex(v.payload),payloads.get(v.name));assert.equal(v.offset,8);
  assert.equal(hex(v.code.slice(v.prefix_bytes)),hex(v.body_code));
 }else {assert.equal(v.program_kind,'checked_add');assert.equal(v.base,66);}
 const e=expected(v),high=await observe(v,Hardfork.Osaka,100000000n);
 assert(agrees(high,e),`${v.name}: high-gas exact behavior ${JSON.stringify({...high,gas:String(high.gas),memory:undefined})}`);
 assert(high.gas>0n);const exact=await observe(v,Hardfork.Osaka,high.gas);
 assert(agrees(exact,e),`${v.name}: exact-gas behavior`);assert.equal(exact.gas,high.gas);
 const short=await observe(v,Hardfork.Osaka,high.gas-1n);
 assert.equal(short.kind,'out of gas',`${v.name}: one-below gas`);assert.equal(short.data,'');
 const zero=await observe(v,Hardfork.Osaka,0n);assert.equal(zero.kind,'out of gas');
 if(v.program_kind==='packet'){
  assert.equal(high.memory.read(7,1)[0],85);assert.equal(high.memory.read(8+v.payload.length,1)[0],119);
  assert.equal(exact.memory.read(7,1)[0],85);assert.equal(exact.memory.read(8+v.payload.length,1)[0],119);
 }
 const historical=[];
 if(v.program_kind==='packet')for(const fork of [Hardfork.Homestead,Hardfork.Byzantium]){
  const r=await observe(v,fork,100000000n);
  if(e.kind==='revert'&&fork===Hardfork.Homestead){assert.equal(r.kind,'invalid opcode');assert.equal(r.data,'');}
  else assert(agrees(r,e),`${v.name}: ${fork} exact behavior`);
  historical.push({fork,kind:r.kind,data:r.data,gas:String(r.gas)});
 }
 rows.push({name:v.name,kind:high.kind,data:high.data,stack:high.stack,codeSha256:sha(Uint8Array.from(v.code)),
   codeBytes:v.code.length,exactGas:String(high.gas),oneBelowKind:short.kind,zeroGasKind:zero.kind,steps:high.steps,historical});
}
const byName=new Map(rows.map(r=>[r.name,r]));
assert.equal(byName.get('return_two').exactGas,byName.get('return_suffix').exactGas);
assert.equal(byName.get('return_two').steps,byName.get('return_suffix').steps);
const positive=vectors.find(v=>v.name==='return_two'),expectPositive=expected(positive);
const alwaysRevert=await observe(vectors.find(v=>v.name==='empty_revert'),Hardfork.Osaka,100000000n);
const alwaysStop=await observe({...positive,code:[0]},Hardfork.Osaka,100000000n);
assert(!agrees(alwaysRevert,expectPositive));assert(!agrees(alwaysStop,expectPositive));
console.log(JSON.stringify({status:'pass',boundary:'External isolated-frame tests; not Lean gas/fork or whole-world proofs',
 fork:'osaka',node:process.version,hostStepLimit:100000,highGasLimit:'100000000',
 versions:Object.fromEntries(['@ethereumjs/evm','@ethereumjs/common','@ethereumjs/util'].map(n=>[n,lock.packages['node_modules/'+n].version])),
 lockSha256:sha(lockBytes),vectorsSha256:sha(raw),provenanceSha256:sha(provenanceBytes),runnerSha256:sha(fs.readFileSync(fileURLToPath(import.meta.url))),
 controls:{alwaysRevertRejected:true,alwaysStopRejected:true,unreachableSuffixIgnored:true},rows}));
