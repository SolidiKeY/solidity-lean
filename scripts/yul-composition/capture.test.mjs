import test from 'node:test';
import assert from 'node:assert/strict';
import {mkdtempSync,chmodSync,writeFileSync,readFileSync}from'node:fs';
import {machine}from'../evm-reference/replay.mjs';
import {Account,createAddressFromString,hexToBytes}from'../evm-reference/node_modules/@ethereumjs/util/dist/esm/index.js';
import {observeMachine,capturedMachine,validateCapture,validateCallCapture,compareState}from'./capture.mjs';
import {execute,checkedCompiler,compileRecord,checkStateOracles,controlFailures}from'./harness.mjs';
const out=mkdtempSync('/workspace/vy5-composition/remaining-20261031/capture-tests-');chmodSync(out,0o755);console.log('state/memory test evidence: '+out);
const save=(name,obj)=>writeFileSync(out+'/'+name+'.json',JSON.stringify(obj,null,2)+'\n');
const self='0x'+'34'.repeat(20),external='0x'+'56'.repeat(20),caller='0x'+'12'.repeat(20),word=n=>'0x'+BigInt(n).toString(16).padStart(64,'0');
async function raw(runtime,balance=0n){const {vm,observer}=await capturedMachine(),a=createAddressFromString(self);await vm.evm.stateManager.putAccount(a,new Account(1n,balance));await vm.evm.stateManager.putCode(a,hexToBytes(runtime));return{vm,observer,a};}
let storageCapture,storageResult,nestedCapture;
test('actual touched storage/account balances/nonces and meaningful LOG memory',async()=>{
 const code='0x602a5f525f515f55600760205fa15f545f5260205ff3';
 const {observer,a}=await raw(code,5n),r=await observer.run({to:a,value:7n},1);storageCapture=r.capture;storageResult=r;save('storage-world-memory',r.capture);
 assert.equal(r.result.execResult.returnValue.length,32);assert.equal(r.result.execResult.returnValue.at(-1),42);
 const oracle={accounts:[{phase:'pre',address:self,fields:{balance:'5',nonce:'1',code}},{phase:'post',address:self,fields:{balance:'12',nonce:'1',code}},{phase:'post',address:caller,fields:{balance:(10n**30n-7n).toString(),nonce:'1'}}],slots:[{phase:'pre',address:self,kind:'persistent',slot:word(0),value:word(0)},{phase:'post',address:self,kind:'persistent',slot:word(0),value:word(42)}],memory:[{depth:0,at:'LOG1',offset:0,bytes:word(42)},{depth:0,at:'final',offset:0,bytes:word(42)}]};
 assert.equal(compareState(r.capture,oracle).status,'match');save('storage-world-memory-oracle',oracle);
 for(const mutate of [c=>c.post[self].persistent[word(0)]=word(41),c=>c.post[self].balance='11',c=>c.post[caller].nonce='0',c=>c.frames[0].memory.bytes='0x'+'00'.repeat(c.frames[0].memory.allocatedBytes)]){const c=structuredClone(r.capture);mutate(c);c.frames[0].post=structuredClone(c.post);assert.equal(compareState(c,oracle).status,'mismatch');assert.deepEqual(c.frames[0].output,r.capture.frames[0].output);}
});
test('missing/reordered/malformed state and frame memory fail closed',()=>{
 for(const mutate of [c=>delete c.post,c=>delete c.frames[0].memory,c=>delete c.pre[self],c=>delete c.post[self].persistent[word(0)],c=>c.events.reverse(),c=>c.operations.reverse(),c=>c.frames[0].memory.bytes='0x1',c=>c.post[self].nonce='-1',c=>c.domain.push(c.domain[0])]) {const c=structuredClone(storageCapture);mutate(c);assert.throws(()=>validateCapture(c));assert.equal(compareState(c,{accounts:[]}).status,'blocked');}
 assert.equal(compareState(storageCapture,null).status,'pending');assert.equal(compareState(storageCapture,{}).status,'blocked');
 assert.equal(compareState(storageCapture,{slots:[{phase:'post',address:self,kind:'persistent',slot:word(999),value:word(0)}]}).status,'blocked');
});
test('accessed external account world and code are captured without expected-slot queries',async()=>{
 const {vm,observer,a}=await raw('0x735656565656565656565656565656565656565656315f5260205ff3');
 const d=createAddressFromString(external);await vm.evm.stateManager.putAccount(d,new Account(7n,123n));await vm.evm.stateManager.putCode(d,hexToBytes('0x00'));
 const r=await observer.run({to:a},1);save('external-world',r.capture);
 assert.equal(compareState(r.capture,{accounts:[{phase:'pre',address:external,fields:{exists:true,balance:'123',nonce:'7',code:'0x00'}},{phase:'post',address:external,fields:{balance:'123',nonce:'7'}}]}).status,'match');
 assert(r.capture.accesses.some(x=>x.address===external&&x.kind==='getAccount'));
});
test('actual nested rollback preserves caller/external world, storage/transient and revert memory',async()=>{
 // External callee writes slots, returns revert bytes77; CALL transfers3 then rolls back.
 const inner='0x60636009556058600a5d604d5f5260205ffd';
 const outer='0x60205f5f5f600373'+'56'.repeat(20)+'620f4240f150602a600455602a5f5260205ff3';
 const {vm,observer,a}=await raw(outer,9n),d=createAddressFromString(external);
 await vm.evm.stateManager.putAccount(d,new Account(1n,0n));await vm.evm.stateManager.putCode(d,hexToBytes(inner));
 const r=await observer.run({to:a},1),c=r.capture;nestedCapture=c;save('nested-rollback',c);
 assert.equal(r.result.execResult.returnValue.at(-1),42);assert.equal(c.frames.length,2);assert.equal(c.frames[1].output.exception,'revert');assert.equal(c.frames[1].output.bytes,word(77));
 const oracle={accounts:[{phase:'post',address:self,fields:{balance:'9'}},{phase:'post',address:external,fields:{balance:'0',nonce:'1'}}],slots:[{phase:'post',address:external,kind:'persistent',slot:word(9),value:word(0)},{phase:'post',address:external,kind:'transient',slot:word(10),value:word(0)},{phase:'post',address:self,kind:'persistent',slot:word(4),value:word(42)}],memory:[{frame:1,at:'final',offset:0,bytes:word(77)},{frame:0,at:'final',offset:0,bytes:word(42)}],buffers:[{frame:0,bytes:word(77)},{frame:1,bytes:'0x'}]};
 assert.equal(compareState(c,oracle).status,'match');assert(c.operations.some(o=>o.kind==='putStorage'&&o.address===external&&o.value===word(99)));assert(c.operations.some(o=>o.kind==='transient.put'&&o.value===word(88)));assert(c.operations.some(o=>o.kind==='revert'));assert(c.operations.some(o=>o.kind==='transient.revert'));
 const mutant=structuredClone(c);mutant.post[external].persistent[word(9)]=word(99);mutant.frames[0].post=structuredClone(mutant.post);assert.equal(compareState(mutant,oracle).status,'mismatch');
});
test('actual transient reset is retained separately from persistent state across transactions',async()=>{
 const {observer,a}=await raw('0x60055c5f52602a60055d60205ff3');
 for(let id=1;id<=2;id++) {const r=await observer.run({to:a},id);save('transient-tx'+id,r.capture);assert.equal(r.result.execResult.returnValue.at(-1),0);assert.equal(r.capture.transaction,id);
  assert.equal(compareState(r.capture,{slots:[{phase:'pre',address:self,kind:'transient',slot:word(5),value:word(0)},{phase:'post',address:self,kind:'transient',slot:word(5),value:word(0)}]}).status,'match');
  assert(r.capture.operations.some(o=>o.kind==='transient.put'&&o.value===word(42)));assert(r.capture.operations.some(o=>o.kind==='transient.clear'&&JSON.stringify(o.value).includes('2a')));
 }
});
test('stateful sequence pre/post slots are captured without independent expected-slot seeding',async()=>{
 const {observer,a}=await raw('0x5f54600101805f555f5260205ff3');
 for(let id=1;id<=2;id++){const r=await observer.run({to:a},id);save('stateful-tx'+id,r.capture);assert.equal(r.result.execResult.returnValue.at(-1),id);assert.equal(compareState(r.capture,{slots:[{phase:'pre',address:self,kind:'persistent',slot:word(0),value:word(id-1)},{phase:'post',address:self,kind:'persistent',slot:word(0),value:word(id)}]}).status,'match');}
});
const fixtures=JSON.parse(readFileSync('tests/yul-composition/fixtures.json')),compile=checkedCompiler('/workspace/vy5-composition/soljson-v0.8.38+commit.1835d247.js');let counter=0;
for(const id of ['memory-storage-logs','try-catch','modifiers','constructors','allocation','dirty-bits','dirty-bits-cleaned'])test('actual compiler profiles retain original bytes and capture state: '+id,async()=>{
 const fixture=fixtures.find(f=>f.id===id);
 for(const viaIR of [false,true])for(const optimized of [false,true]) {
  const input={language:'Solidity',sources:{'case.sol':{content:fixture.source}},settings:{viaIR,evmVersion:'osaka',optimizer:{enabled:optimized,runs:200},metadata:{appendCBOR:false},outputSelection:{'*':{'*':['abi','evm.bytecode.object','evm.deployedBytecode.object','evm.methodIdentifiers']}}}};
  const {output,errors}=compileRecord(compile,input,out+'/compile-'+counter++);assert.equal(errors.length,0);
  const result=await execute(output.contracts['case.sol'].C,fixture);save(id+'-'+viaIR+'-'+optimized,result);validateCapture(result.observed.capture);
  if(fixture.expected)assert.equal(result.observed.returnData,fixture.expected.returnData);
  if(['memory-storage-logs','try-catch','modifiers','constructors'].includes(id))assert.equal(result.stateComparison.status,'match');else assert.equal(result.stateComparison.status,'pending');
 }
});

test('malformed/vacuous oracles are blocked rather than exceptions or matches',()=>{
 for(const oracle of [{accounts:[null]},{accounts:[{phase:'post',address:self,fields:{}}]},{accounts:[{phase:'post',address:self,fields:null}]},{slots:[null]},{slots:[{phase:'post',address:self,kind:'wrong',slot:word(0),value:word(42)}]},{memory:[null]},{memory:[{at:'final',offset:0,bytes:word(42)}]},{memory:[{frame:0,at:'final',offset:0,bytes:word(42),count:0}]},false])assert.equal(compareState(storageCapture,oracle).status,'blocked');
});
test('frame worlds and capture/result identity cannot be dropped or swapped',()=>{
 for(const mutate of [c=>{c.frames[0].pre={};c.frames[0].post={};},c=>delete c.frames[0].post[self].persistent[word(0)],c=>c.frames[0].input='0x01']){const c=structuredClone(storageCapture);mutate(c);assert.throws(()=>validateCapture(c));}
 const actual={failed:false,exception:null,returnData:word(42),metrics:storageResult.metrics,logs:storageCapture.frames[0].output.logs};validateCallCapture(storageCapture,actual,{transaction:1,value:'7',to:self,input:'0x',caller});
 for(const mutate of [a=>a.returnData=word(41),a=>a.exception='revert',a=>a.metrics.steps++]){const a=structuredClone(actual);mutate(a);assert.throws(()=>validateCallCapture(storageCapture,a));}
 assert.throws(()=>validateCallCapture(storageCapture,actual,{transaction:2}));
});
test('unknown preinstallation persistent slot after clear is blocked, not fabricated zero',async()=>{
 const vm=await machine(),a=createAddressFromString(self);await vm.evm.stateManager.putStorage(a,hexToBytes(word(7)),hexToBytes(word(99)));
 const observer=observeMachine(vm);
 await assert.rejects(()=>observer.run({to:a},1,async()=>{await vm.evm.stateManager.clearStorage(a);await vm.evm.stateManager.getStorage(a,hexToBytes(word(7)));}),/unknown persistent pre-value/);
});
test('transient preinstallation domain is seeded through public toJSON before reset',async()=>{
 const vm=await machine(),a=createAddressFromString(self);vm.evm.transientStorage.put(a,hexToBytes(word(7)),hexToBytes(word(99)));
 const observer=observeMachine(vm),r=await observer.run({to:a},1,()=>vm.evm.transientStorage.clear());
 assert.equal(r.capture.pre[self].transient[word(7)],word(99));assert.equal(r.capture.post[self].transient[word(7)],word(0));save('transient-preinstalled',r.capture);
});
test('required source-bound state oracle rows cannot disappear or silently become pending',()=>{
 const raw=readFileSync('tests/yul-composition/state-oracles.json','utf8'),rows=checkStateOracles(raw);assert.equal(rows.length,7);
 for(const bad of [rows.slice(1),[...rows,rows[0]],rows.map(r=>({...r,sourceSha256:'bad'}))])assert.throws(()=>checkStateOracles(JSON.stringify(bad)));
 assert(controlFailures([{id:'memory-storage-logs',kind:'combination',status:'match'}],true).some(s=>s.includes('state comparison')));
});

test('nested frame code/storage context metadata cannot be omitted',()=>{
 for(const key of ['kind','codeAddress','delegatecall','isStatic','createdAddress']) {
  const c=structuredClone(nestedCapture);delete c.frames[1][key];assert.throws(()=>validateCapture(c),/frame context/);
 }
});

test('returndata register is distinct from frame output, memory and rolled-back world',()=>{
 assert.equal(nestedCapture.frames[0].lastCallReturnData.bytes,word(77));assert.equal(nestedCapture.frames[0].output.bytes,word(42));
 assert.equal(nestedCapture.frames[1].output.exception,'revert');assert.equal(nestedCapture.post[external].persistent[word(9)],word(0));
 const oracle={buffers:[{frame:0,bytes:word(77)}]},c=structuredClone(nestedCapture);c.frames[0].lastCallReturnData.bytes=word(42);assert.equal(compareState(c,oracle).status,'mismatch');
 delete c.frames[0].lastCallReturnData;assert.throws(()=>validateCapture(c),/returndata/);assert.equal(compareState(c,oracle).status,'blocked');
 assert.equal(compareState(nestedCapture,{buffers:[{frame:99,bytes:'0x'}]}).status,'blocked');
});
