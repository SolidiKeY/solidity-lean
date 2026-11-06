import test from'node:test';import assert from'node:assert/strict';
import{readFileSync,writeFileSync,mkdtempSync,chmodSync}from'node:fs';import{keccak_256}from'../evm-reference/node_modules/@noble/hashes/sha3.js';
import{checkedCompiler,compileRecord}from'./harness.mjs';import{runFixture,validateFixtureEvidence,HOST}from'./upstream.mjs';import{compareUpstreamState,predictedAliases,create2Aliases}from'./oracles.mjs';import{validateBoundary}from'./capture.mjs';
const out=mkdtempSync('/workspace/vy5-composition/remaining-20261031/remaining-tests-');chmodSync(out,0o755);console.log('remaining oracle evidence: '+out);
const compiler=checkedCompiler('/workspace/vy5-composition/soljson-v0.8.38+commit.1835d247.js');let n=0;const compile=i=>compileRecord(compiler,i,out+'/compile-'+n++).output;
const names=['calldata_assign.sol','calldata_assign_from_nowhere.sol','calldata_length_read.sol','calldata_offset_read.sol','calldata_offset_read_write.sol','calldata_struct_assign.sol','calldata_struct_assign_and_return.sol','keccak256_optimizer_cache_bug.sol','external_function_pointer_selector.sol','selfbalance.sol','transient_storage_low_level_calls.sol','transient_storage_selfdestruct.sol'],cases=new Map(),word=n=>'0x'+BigInt(n).toString(16).padStart(64,'0');
for(const name of names)test('new complete ordered source assertions: '+name,async()=>{
 const r=await runFixture('test/libsolidity/semanticTests/inlineAssembly/'+name,'/workspace/vy5-composition/corpus',compile);cases.set(name,r);writeFileSync(out+'/'+name+'.json',JSON.stringify(r,null,2));assert.equal(r.status,'working');validateFixtureEvidence(r,'/workspace/vy5-composition/corpus');for(const v of r.variants)assert.equal(v.stateComparison.status,'match',JSON.stringify(v.stateComparison));
});
function reject(name,fn){const r=cases.get(name),v=structuredClone(r.variants[0]);fn(v);const result=compareUpstreamState(r,v,HOST.sender);assert(['blocked','mismatch'].includes(result.status),JSON.stringify(result));return result;}
function memory(v,call,offset){const r=v.observed[call].capture.frames[0].regions.find(r=>r.opcode==='RETURN'),b=Buffer.from(r.bytes.slice(2),'hex');b[Number(r.offset)+offset]^=1;r.bytes='0x'+b.toString('hex');}
test('wrong calldata offsets/lengths/selector bytes/struct aliases fail with unchanged outputs',()=>{
 for(const [name,call,offset]of [['calldata_assign.sol',0,64],['calldata_assign_from_nowhere.sol',0,64],['calldata_length_read.sol',2,31],['calldata_offset_read.sol',1,31],['calldata_offset_read_write.sol',1,63],['calldata_struct_assign.sol',0,31],['calldata_struct_assign_and_return.sol',0,31]])reject(name,v=>memory(v,call,offset));
 reject('calldata_length_read.sol',v=>{[v.observed[0],v.observed[1]]=[v.observed[1],v.observed[0]];});reject('calldata_assign.sol',v=>{const o=v.observed[0];o.requestData='0xdeadbeef';o.capture.request.input=o.requestData;o.capture.frames[0].input=o.requestData;});
});
test('Fixed hash slots, selector alignment, funding and host nonce are independently constrained',()=>{
 reject('keccak256_optimizer_cache_bug.sol',v=>{const c=v.observed[0].capture,a=predictedAliases(HOST.sender).self,slot=Object.keys(c.post[a].persistent).find(k=>c.post[a].persistent[k]===word(234));c.post[a].persistent[slot]=word(123);c.frames[0].post=structuredClone(c.post);});
 reject('external_function_pointer_selector.sol',v=>memory(v,0,0));reject('selfbalance.sol',v=>{const c=v.observed[0].capture;c.post[HOST.sender].balance=(BigInt(HOST.funding)-253n).toString();c.frames[0].post=structuredClone(c.post);});
});
test('CREATE2 bytes32 literal salts and address formula are independent of VM returned targets',()=>{
 const v=cases.get('transient_storage_low_level_calls.sol').variants[0],init=v.oracleInputs.create2Initcode,a=create2Aliases(HOST.sender,init),self=predictedAliases(HOST.sender).self;
 for(let salt=0;salt<4;salt++){const saltWord=salt.toString(16).padStart(2,'0').padEnd(64,'0'),expected='0x'+Buffer.from(keccak_256(Buffer.concat([Buffer.from('ff'+self.slice(2)+saltWord,'hex'),Buffer.from(keccak_256(Buffer.from(init.slice(2),'hex')))]))).subarray(12).toString('hex');assert.equal(a['create2:'+salt],expected);}
 const numeric='0x'+Buffer.from(keccak_256(Buffer.concat([Buffer.from('ff'+self.slice(2)+word(1).slice(2),'hex'),Buffer.from(keccak_256(Buffer.from(init.slice(2),'hex')))]))).subarray(12).toString('hex');assert.notEqual(a['create2:1'],numeric);
});
test('CREATE2 nested initcode/runtime/target owner and input/profile receipts cannot be forged',()=>{
 const name='transient_storage_low_level_calls.sol';
 reject(name,v=>v.observed[1].capture.frames.find(f=>f.kind==='create').input='0x00');
 reject(name,v=>v.oracleInputs.inputSha256='stale');reject(name,v=>v.oracleInputs.create2Initcode='0x00');reject(name,v=>v.artifactHashes.D.runtime='0'.repeat(64));
 reject(name,v=>{const a=create2Aliases(HOST.sender,v.oracleInputs.create2Initcode),c=v.observed[1].capture; c.post[a['create2:1']].nonce='2';c.frames[0].post=structuredClone(c.post);});
 reject(name,v=>{const a=create2Aliases(HOST.sender,v.oracleInputs.create2Initcode),o=v.observed[1].capture.operations.find(o=>o.kind==='transient.put'&&o.address===a['create2:1']);o.address=a.self;});
 const r=structuredClone(cases.get(name));r.variants[0].settings.viaIR=!r.variants[0].settings.viaIR;assert.throws(()=>validateFixtureEvidence(r,'/workspace/vy5-composition/corpus'));
});
test('actual host cleanup deletes only newly created child without extra source call/runTx',()=>{
 const r=cases.get('transient_storage_selfdestruct.sol'),a=predictedAliases(HOST.sender);
 for(const v of r.variants){const c=v.postPlanCleanup;validateBoundary(c);assert.equal(v.observed.length,3);assert.equal(c.nextCallOrdinal,4);assert(!Object.hasOwn(c,'frames'));assert(c.pre[a.child2].exists);assert(!c.post[a.child2].exists);assert(c.post[a.child].exists);assert.deepEqual(c.effects.deletedAccounts,[a.child2]);assert.equal(v.stateComparison.cleanup.status,'match');}
});
test('missing/wrong/malformed/deordered cleanup evidence cannot match despite equal original outputs',()=>{
 const name='transient_storage_selfdestruct.sol';for(const fn of [v=>delete v.postPlanCleanup,v=>v.postPlanCleanup.effects.deletedAccounts=[],v=>v.postPlanCleanup.nextCallOrdinal=99,v=>v.postPlanCleanup.operations.reverse(),v=>v.postPlanCleanup.operations.find(o=>o.kind==='transient.clear').value='garbage',v=>v.postPlanCleanup.effects.transientBeforeReset={bad:{}},v=>v.postPlanCleanup.operations.find(o=>o.kind==='putCode').value='not-bytes',v=>v.postPlanCleanup.post[predictedAliases(HOST.sender).child2].exists=true])reject(name,fn);
});
