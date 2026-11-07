import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync,writeFileSync,mkdtempSync,chmodSync}from'node:fs';
import {createHash}from'node:crypto';
import {keccak_256}from'../evm-reference/node_modules/@noble/hashes/sha3.js';
import {predictedAliases,compareLocalState,compareUpstreamState,checkStateOracles,checkUpstreamOracles}from'./oracles.mjs';
import {validateCapture,capturedMachine}from'./capture.mjs';
import {Account,createAddressFromString,hexToBytes}from'../evm-reference/node_modules/@ethereumjs/util/dist/esm/index.js';
import {execute,checkedCompiler,compileRecord,inputFor,controlFailures}from'./harness.mjs';
import {runFixture,validateFixtureEvidence,HOST}from'./upstream.mjs';
const out=mkdtempSync('/workspace/vy5-composition/remaining-20261031/oracle-tests-');chmodSync(out,0o755);console.log('independent oracle evidence: '+out);
const compiler=checkedCompiler('/workspace/vy5-composition/soljson-v0.8.38+commit.1835d247.js');let counter=0;
const compile=i=>compileRecord(compiler,i,out+'/compile-'+counter++).output;
const fixtures=JSON.parse(readFileSync('tests/yul-composition/fixtures.json')),word=n=>'0x'+BigInt(n).toString(16).padStart(64,'0'),aliases=predictedAliases();
const records=new Map();const save=(n,r)=>writeFileSync(out+'/'+n+'.json',JSON.stringify(r,null,2)+'\n');
function consistent(record,fn){const r=structuredClone(record),c=r.observed.capture;fn(r,c);c.frames[0].post=structuredClone(c.post);return r;}
function reject(id,record){const f=fixtures.find(f=>f.id===id),r=compareLocalState(f,record);assert(['mismatch','blocked'].includes(r.status),JSON.stringify(r));return r;}
test('CREATE root nonce0 and child nonce1 predictions match independent short RLP/Keccak formula',()=>{
 for(const caller of ['0x'+'12'.repeat(20),HOST.sender,'0x'+'ab'.repeat(20)]) {
  const p=predictedAliases(caller),create=(a,n)=>'0x'+Buffer.from(keccak_256(Buffer.from('d694'+a.slice(2)+(n===0?'80':'01'),'hex'))).subarray(12).toString('hex');
  assert.equal(p.self,create(caller,0));assert.equal(p.child,create(p.self,1));
 }
});
test('local and upstream registration hashes reject missing/stale/reordered oracle rows',()=>{
 for(const [file,check,count]of [['state-oracles.json',checkStateOracles,7],['upstream-state-oracles.json',checkUpstreamOracles,73]]){
  const raw=readFileSync('tests/yul-composition/'+file,'utf8'),rows=check(raw);assert.equal(rows.length,count);
  for(const mutation of [r=>r.pop(),r=>r.reverse(),r=>r[0].sourceSha256='bad']){const bad=structuredClone(rows);mutation(bad);assert.throws(()=>check(JSON.stringify(bad)));}
 }
});
for(const id of ['mixed-logs','new-constructor','constructor-failure'])test('source-derived independent local oracle, all four compiler profiles: '+id,async()=>{
 const fixture=fixtures.find(f=>f.id===id);
 for(const pipeline of ['legacy','viaIR'])for(const optimized of [false,true]) {
  const output=compile(inputFor({'case.sol':{content:fixture.source}},pipeline,optimized));assert(!(output.errors??[]).some(e=>e.severity==='error'));
  const r=await execute(output.contracts['case.sol'].C,fixture);save(id+'-'+pipeline+'-'+optimized,r);records.set(id,r);
  assert.equal(r.stateComparison.status,'match',JSON.stringify(r.stateComparison));assert.equal(r.executionKind,'runCall');assert.equal(r.phase,fixture.deploymentOnly?'deployment':'runtime');
  assert.equal(r.observed.returnData,fixture.expected.returnData);assert.equal(r.observed.exception,fixture.expected.exception);
  const row={...r,id,kind:'combination',pipeline,optimized,status:'match'};assert(!controlFailures([row],true).some(s=>s.startsWith(id+':')));
  for(const mutate of [x=>delete x.stateComparison,x=>x.stateComparison={status:'match'},x=>delete x.phase,x=>delete x.executionKind]){const bad=structuredClone(row);mutate(bad);assert(controlFailures([bad],true).some(s=>s.startsWith(id+':')));}
 }
});
test('mixed logs preserve order, emitter and two meaningful windows without pointer equality',()=>{
 const original=records.get('mixed-logs'),f=fixtures.find(f=>f.id==='mixed-logs');assert.equal(original.observed.rawLogs.length,2);
 for(const mutate of [(r,c)=>{r.observed.logs.reverse();r.observed.rawLogs.reverse();c.frames[0].output.logs.reverse();},(r,c)=>{const region=c.frames[0].regions.find(r=>r.opcode==='LOG0'),b=Buffer.from(region.bytes.slice(2),'hex');b.set(Buffer.from(word(99).slice(2),'hex'),Number(region.offset));region.bytes='0x'+b.toString('hex');},(r,c)=>c.frames[0].regions=[],(r,c)=>delete c.frames[0].regions[0].phase])reject('mixed-logs',consistent(original,mutate));
 assert.equal(compareLocalState({...f,source:f.source+' '},original).status,'blocked');
});
test('created child address, nonce, balance, storage, getter frame and installation cannot be inferred or omitted',()=>{
 const original=records.get('new-constructor');assert.equal(original.observed.capture.frames[1].createdAddress,aliases.child);
 for(const mutate of [(r,c)=>c.post[aliases.child].persistent[word(0)]=word(41),(r,c)=>c.post[aliases.child].nonce='2',(r,c)=>c.post[aliases.child].balance='1',(r,c)=>c.post[aliases.self].nonce='1',(r,c)=>c.frames[1].createdAddress=aliases.self,(r,c)=>c.frames[2].input='0x00000000',(r,c)=>c.frames.reverse(),(r,c)=>delete c.frames[1].post[aliases.child],(r,c)=>{c.post[aliases.child].code='0x00';c.post[aliases.child].codeSha256=createHash('sha256').update(Buffer.from([0])).digest('hex');}])reject('new-constructor',consistent(original,mutate));
 const missing=structuredClone(original);delete missing.deploymentCapture;reject('new-constructor',missing);
});
test('failed CREATE retains no candidate account/code/slots/logs; caller nonce belongs to runCall boundary',()=>{
 const original=records.get('constructor-failure'),c=original.observed.capture;assert.equal(c.post[aliases.self].exists,false);assert.equal(c.pre[aliases.caller].nonce,'0');assert.equal(c.post[aliases.caller].nonce,'1');
 for(const mutate of [(r,c)=>c.post[aliases.self].exists=true,(r,c)=>c.post[aliases.caller].nonce='0',(r,c)=>{c.post[aliases.self].code='0x00';c.post[aliases.self].codeSha256=createHash('sha256').update(Buffer.from([0])).digest('hex');},(r,c)=>c.operations=c.operations.filter(o=>o.kind!=='revert').map((o,i)=>({...o,sequence:i})),(r,c)=>delete c.frames[0].memory,(r,c)=>r.executionKind='runTx',(r,c)=>r.deployment.candidateAddress=aliases.child,(r,c)=>{r.observed.logs=[{emitter:aliases.self,topics:[],data:'0x'}];c.frames[0].output.logs=structuredClone(r.observed.logs);}]) {
  const bad=consistent(original,mutate);bad.deploymentCapture=bad.observed.capture;reject('constructor-failure',bad);
 }
});
test('touched-slot domain cannot be erased in coordination with every frame snapshot',()=>{
 const original=records.get('new-constructor'),bad=consistent(original,(r,c)=>{c.domain.find(d=>d.address===aliases.child).persistent=[];for(const w of [c.pre,c.post,...c.frames.flatMap(f=>[f.pre,f.post])])if(w[aliases.child])w[aliases.child].persistent={};});assert.throws(()=>validateCapture(bad.observed.capture),/slot.*domain/);
});
const corpus='/workspace/vy5-composition/corpus',upstream=new Map();
for(const name of ['slot_access.sol','inline_assembly_memory_access.sol','optimize_memory_store_multi_block.sol','optimize_memory_store_multi_block_bugreport.sol','transient_storage_creation.sol'])test('pinned upstream source-derived state/window oracle: '+name,async()=>{
 const path='test/libsolidity/semanticTests/inlineAssembly/'+name,r=await runFixture(path,corpus,compile);save(name,r);upstream.set(name,r);
 assert.equal(r.status,'working');validateFixtureEvidence(r,corpus);for(const v of r.variants)assert.equal(v.stateComparison.status,'match',JSON.stringify(v.stateComparison));
});
test('upstream state oracle rejects wrong slots/window, omitted calls and hidden mismatches',()=>{
 const source=upstream.get('slot_access.sol'),v=structuredClone(source.variants[0]),o=v.observed[0],slot=Object.keys(o.capture.post[predictedAliases(HOST.sender).self].persistent)[0];
 o.capture.post[predictedAliases(HOST.sender).self].persistent[slot]=word(9);o.capture.frames[0].post=structuredClone(o.capture.post);
 assert.equal(compareUpstreamState(source,v,HOST.sender).status,'mismatch');delete v.observed[1].capture;assert.equal(compareUpstreamState(source,v,HOST.sender).status,'mismatch');
 const missing=structuredClone(source);delete missing.variants[0].stateComparison;assert.throws(()=>validateFixtureEvidence(missing,corpus));
 const stale=structuredClone(source);stale.sourceSha256='wrong';assert.equal(compareUpstreamState(stale,source.variants[0],HOST.sender).status,'blocked');
 const malformed=structuredClone(source);malformed.variants[0].observed.reverse();assert.throws(()=>validateFixtureEvidence(malformed,corpus));
 const memory=structuredClone(upstream.get('inline_assembly_memory_access.sol'));const reg=memory.variants[0].observed[0].capture.frames[0].regions[0];reg.bytes='0x'+'00'.repeat(reg.allocatedBytes);assert.equal(compareUpstreamState(memory,memory.variants[0],HOST.sender).status,'mismatch');
});

test('minimal-byte transient JSON payload decodes as exact expected word42; wrong payload fails',()=>{
 const r=JSON.parse(readFileSync(out+'/transient_storage_creation.sol.json')),v=structuredClone(r.variants[0]),clear=v.observed[0].capture.operations.find(o=>o.kind==='transient.clear'&&Object.keys(o.value).length);
 assert.equal(compareUpstreamState(r,v,HOST.sender).status,'match');const a=predictedAliases(HOST.sender).self;assert.equal(clear.value[a][word(0)],'0x2a');
 clear.value[a][word(0)]='0x2b';assert.equal(compareUpstreamState(r,v,HOST.sender).status,'mismatch');clear.value[a][word(0)]='not-bytes';assert.equal(compareUpstreamState(r,v,HOST.sender).status,'blocked');
});
test('third-party account reads bind nested frame worlds without requiring world enumeration',async()=>{
 const {vm,observer}=await capturedMachine(),a='0x'+'34'.repeat(20),b='0x'+'56'.repeat(20),e='0x'+'78'.repeat(20);
 for(const address of [a,b,e])await vm.evm.stateManager.putAccount(createAddressFromString(address),new Account(1n,address===e?7n:0n));
 await vm.evm.stateManager.putCode(createAddressFromString(b),hexToBytes('0x73'+e.slice(2)+'315000'));
 await vm.evm.stateManager.putCode(createAddressFromString(a),hexToBytes('0x5f5f5f5f5f73'+b.slice(2)+'620f4240f15000'));
 const result=await observer.run({to:createAddressFromString(a)},1),c=result.capture;assert.equal(c.frames[1].pre[e].balance,'7');save('third-party-frame',c);
 const bad=structuredClone(c);delete bad.frames[1].pre[e];delete bad.frames[1].post[e];assert.throws(()=>validateCapture(bad),/accessed account.*frame domain/);
});

test('required selected upstream oracle cannot disappear into a blocked profile',()=>{
 const r=structuredClone(upstream.get('slot_access.sol'));r.variants[0].status='blocked';r.variants[0].reason='capture unavailable';delete r.variants[0].stateComparison;r.status='blocked';assert.throws(()=>validateFixtureEvidence(r,corpus),/required upstream state control/);
});
