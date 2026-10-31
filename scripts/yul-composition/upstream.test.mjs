import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync,mkdirSync,writeFileSync,mkdtempSync,chmodSync}from'node:fs';
import {join}from'node:path';
import {parseFixture,semanticVectors}from'../solidity-upstream.mjs';
import {checkedCompiler,compileRecord,ROOT}from'./harness.mjs';
import {parseExpectations,parseLog,profilesFor,exactObservation,compareCall,runFixture,replay,validateFixtureEvidence,osakaCompatible}from'./upstream.mjs';
const directory='/workspace/vy5-composition/corpus';
const out=mkdtempSync('/workspace/vy5-composition/physical-20261031/upstream-tests-');chmodSync(out,0o755);console.log('test evidence: '+out);
const compileRaw=checkedCompiler('/workspace/vy5-composition/soljson-v0.8.38+commit.1835d247.js');
let counter=0;const compile=input=>compileRecord(compileRaw,input,join(out,'compile-'+counter++)).output;
const path=name=>'test/libsolidity/semanticTests/inlineAssembly/'+name;
function plan(name){return parseExpectations(parseFixture(readFileSync(join(directory,path(name)),'utf8')).expectations);}
test('omitted arrow, call sequence, value and gas metadata are retained',()=>{
 const p=parseExpectations(['set(uint256): 4','get() -> 4','gas legacy: 12','gas irOptimized code: 20','f(), 254 wei -> 254']);
 assert.equal(p.calls.length,3);assert.equal(p.records.length,5);assert.deepEqual(p.calls[0].expectedBytes,[]);
 assert.equal(p.calls[0].calldata.length,32);assert.equal(p.calls[1].gas.length,2);assert(p.calls[1].gas.every(g=>g.semanticObservation===false));assert.equal(p.calls[2].value,'254');
});
test('anonymous log data/topics/emitter order is exact',()=>{
 const l=parseLog('~ emit <anonymous> from 0x'+'12'.repeat(20)+': #0x07, 0x2a');
 assert.equal(l.topics[0],'0x'+'0'.repeat(63)+'7');assert.equal(l.data,'0x'+'0'.repeat(62)+'2a');assert.equal(l.emitter,'0x'+'12'.repeat(20));
 const c=parseExpectations(['f() ->','~ emit <anonymous>: 1','~ emit <anonymous>: 2']).calls[0];
 const self='0x'+'34'.repeat(20);const actual={failed:false,exception:null,returnData:'0x',logs:c.logs.map(l=>({...l,emitter:self}))};
 assert.equal(compareCall(c,actual,self).status,'working');
 actual.logs.reverse();assert.equal(compareCall(c,actual,self).status,'broken');
});
test('malformed or missing evidence cannot become an empty observation',()=>{
 for(const lines of [['gas legacy: 2'],['~ emit <anonymous>: 1'],['f():'],['f() -> FAILURE bad'],['nonsense'],['f() ->','gas unknown: 2']])assert.throws(()=>parseExpectations(lines));
 const e={returnValue:new Uint8Array(),executionGasUsed:1n};assert.throws(()=>exactObservation(e,{}));
 e.logs=[];e.exceptionError={error:'unknown engine failure'};assert.throws(()=>exactObservation(e,{}));
 assert.throws(()=>compareCall(plan('clz.sol').calls[0],{},'self'));
});
test('runtime profiles preserve required pipelines and classify metadata profiles',()=>{
 const p=parseExpectations(['f() ->','gas irOptimized: 1','gas ssaCFGOptimized: 2']);
 const profiles=profilesFor({settings:{compileViaYul:'also'}},p);
 assert.deepEqual(profiles.filter(p=>p.required).map(p=>p.pipeline),['legacy','viaIR','viaIR']);
 assert.equal(profiles.find(p=>p.name==='irOptimized').optimized,true);assert.equal(profiles.find(p=>p.name==='ssaCFGOptimized').ssaCFG,true);
 assert(profilesFor({settings:{compileViaYul:'true'}},parseExpectations(['f() ->','gas legacy: 2'])).find(p=>p.name==='legacy').blocked);
 assert(osakaCompatible('<amsterdam'));assert(!osakaCompatible('<cancun'));assert.throws(()=>osakaCompatible('<unknownFork'));
});
let clzResult;
test('real clz bytes32 vector reproduces old missing-args shape and now executes',async()=>{
 const prior=JSON.parse(readFileSync('/workspace/vy5-composition/reviewed-reference/upstream-clz.sol-legacy.reference-0.output.json'));
 const f=parseFixture(readFileSync(join(directory,path('clz.sol')),'utf8'));const v=semanticVectors(f,prior.contracts[''].C.abi);
 assert(!Object.hasOwn(v[0],'args'));assert.equal(v[0].expectedBytes.length,32);
 clzResult=await runFixture(path('clz.sol'),directory,compile);assert.equal(clzResult.status,'working');
 assert.equal(validateFixtureEvidence(clzResult,directory).calls,3);for(const v of clzResult.variants)assert.equal(v.observed.length,3);
});
for(const name of ['constant_access.sol','inline_assembly_function_call.sol','calldata_array_assign_dynamic.sol','slot_access.sol','optimize_memory_store_multi_block_bugreport.sol','keccak_yul_optimization.sol','blobhash.sol','prevrandao.sol','chainid.sol','selfbalance.sol','transient_storage_multiple_calls_different_transactions.sol'])test('complete real fixture: '+name,async()=>{
 const r=await runFixture(path(name),directory,compile);assert.equal(r.status,'working',JSON.stringify(r.variants.map(v=>v.reason)));
 validateFixtureEvidence(r,directory);for(const v of r.variants){assert.equal(v.observed.length,r.plan.calls.length);assert(v.observed.every(o=>o.comparison.status==='working'));}
 writeFileSync(join(out,name+'.report.json'),JSON.stringify(r,null,2));
 if(name==='slot_access.sol')assert.deepEqual(r.variants[0].observed.map(o=>o.signature),['get()','mappingAccess(uint256)','set(uint256)','get()','mappingAccess(uint256)']);
 if(name==='optimize_memory_store_multi_block_bugreport.sol')assert.equal(r.variants[0].observed[0].actual.logs.length,1);
 if(name==='selfbalance.sol')assert.equal(r.variants[0].observed[0].value,'254');
 if(name==='transient_storage_multiple_calls_different_transactions.sol')assert.deepEqual(r.variants[0].observed[1].frame.transientBeforeReset,{});
});
test('report evidence rejects omitted/malformed profile, call and expectation records',()=>{
 assert(clzResult);
 for(const mutation of ['profile','duplicate','call','actual','bytes','oracle','status','deployment','metrics']){
  const r=structuredClone(clzResult);
  if(mutation==='deployment')delete r.variants[0].deployment;if(mutation==='metrics')delete r.variants[0].observed[0].actual.metrics;
  if(mutation==='profile')r.variants.pop();if(mutation==='duplicate')r.variants[1]=r.variants[0];
  if(mutation==='call')r.variants[0].observed.pop();if(mutation==='actual')delete r.variants[0].observed[0].actual.logs;
  if(mutation==='bytes')r.variants[0].observed[0].inputBytes='0x42';if(mutation==='oracle')r.originalExpectations[0]='f() -> 7';if(mutation==='status')r.status='blocked';
  assert.throws(()=>validateFixtureEvidence(r,directory),mutation);
 }
});
function artifact(source){const o=compile({language:'Solidity',sources:{'c.sol':{content:'pragma solidity ^0.8.38; '+source}},settings:{evmVersion:'osaka',outputSelection:{'*':{'*':['abi','evm.bytecode.object','evm.deployedBytecode.object','evm.methodIdentifiers']}}}});assert(!(o.errors??[]).some(e=>e.severity==='error'));return o.contracts['c.sol'].C;}
test('a mismatch followed by a blocked call cannot be downgraded',async()=>{
 const a=artifact('contract C { function f() external pure returns(uint){return 42;} }');
 const r=await replay(a,parseExpectations(['f() -> 41','missing() ->']));
 assert.equal(r.status,'broken');assert.equal(r.blockedCall,1);assert.equal(r.observed[0].comparison.status,'broken');
});
test('actual EIP-6780 finalization deletes newly-created but keeps old code',async()=>{
 const a=artifact('contract D {function die() external {selfdestruct(payable(msg.sender));} function f()external pure returns(uint){return 42;}} contract C {D d;D old; function make()external{d=new D();d.die();assert(address(d).code.length>0);} function size()external view returns(uint){return address(d).code.length;} function makeOld()external{old=new D();} function killOld()external{old.die();} function oldValue()external returns(uint){return old.f();}}');
 const r=await replay(a,parseExpectations(['make() ->','size() -> 0','makeOld() ->','killOld() ->','oldValue() -> 42']));
 writeFileSync(join(out,'selfdestruct-frames.actual.json'),JSON.stringify(r,null,2));
 assert.equal(r.status,'working',r.reason);assert.equal(r.observed[1].frame.deletedAccounts.length,1);assert.equal(r.observed[4].frame.deletedAccounts.length,0);
 const deleted=r.observed[1].frame.deletedAccounts[0],capture=r.observed[1].capture;
 assert(capture.operations.some(o=>o.kind==='deleteAccount'&&o.address===deleted));
 assert.equal(capture.pre[deleted].exists,true);assert.equal(capture.post[deleted].exists,false);assert.equal(capture.post[deleted].code,'0x');
 writeFileSync(join(out,'selfdestruct-frames.report.json'),JSON.stringify(r,null,2));
});

test('coordinated oracle changes cannot replace pinned expectations',()=>{
 const r=structuredClone(clzResult);r.originalExpectations[0]='f() -> 42';r.plan=parseExpectations(r.originalExpectations);
 assert.throws(()=>validateFixtureEvidence(r,directory),/pinned settings\/expectations/);
 assert.throws(()=>validateFixtureEvidence(clzResult),/corpus directory/);
});

test('deployment and compiler metadata evidence fail closed',()=>{
 for(const mutate of [r=>r.variants[0].deployment.actual.logs.push({emitter:'0x'+'12'.repeat(20),topics:[],data:'0x'}),r=>r.variants[0].deployment.actual.exception='unknown',r=>delete r.variants[0].deployment.actual.metrics,r=>r.variants[0].settings.viaIR=true,r=>r.variants[0].inputSha256='bad']) {
  const r=structuredClone(clzResult);mutate(r);assert.throws(()=>validateFixtureEvidence(r,directory));
 }
});
