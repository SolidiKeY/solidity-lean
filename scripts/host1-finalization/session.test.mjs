import test from 'node:test';
import assert from 'node:assert/strict';
import {createFinalizationSession,validateFinalizedMessage,parseAddress,parseWord,parseBytes,CALLER,Host1Blocked,readObservedAccount,readObservedSlot} from './index.mjs';
import {createContractAddress,createAddressFromString} from '../evm-reference/node_modules/@ethereumjs/util/dist/esm/index.js';
const A='0x'+'00'.repeat(18)+'0abc',B='0x'+'00'.repeat(18)+'beef',EMPTY='0x'+'00'.repeat(18)+'cafe';
const W=n=>'0x'+BigInt(n).toString(16).padStart(64,'0');
const M=10n**30n;
const seed=(address,code,balance=0n,nonce=1n,storage={})=>({address,code,balance,nonce,storage});
const request=(id,to,data='0x',value=0n)=>({id,kind:'call',to,data,value});
async function run(session,req,n){const r=await session.execute(req);validateFinalizedMessage(r,req,n);return r;}
test('actual source pins, branded parsers and full phase-state write',async()=>{
 const code='0x602a5f5500',s=await createFinalizationSession({seeds:[seed(A,code,7n)]}),q=request('write',A),r=await run(s,q,0);
 assert.equal(parseAddress(A),A);assert.equal(parseWord(W(0)),W(0));assert.equal(parseBytes('0xdead'),'0xdead');
 assert.equal(r.pre[CALLER].nonce,'0');assert.equal(r.post[CALLER].nonce,'1');assert.equal(r.post[CALLER].balance,M.toString());
 assert.equal(r.pre[A].persistent[W(0)],W(0));assert.equal(r.messagePost[A].persistent[W(0)],W(42));assert.equal(r.post[A].persistent[W(0)],W(42));assert.equal(r.post[A].code,code);
 assert.equal(r.message.bytes,'0x');assert.equal(r.message.exception,null);assert.deepEqual(r.finalization.eligible,[]);assert.equal(r.environment.transactionEnvelope,false);assert.equal(r.environment.feeAccounting,false);
 assert.ok(Object.isFrozen(r.post[A]));assert.throws(()=>r.post[A].balance='0');
 await assert.rejects(s.execute(q),Host1Blocked);
});
test('preexisting SELFDESTRUCT retains full code/storage/nonce and transfers balance',async()=>{
 const code='0x73'+B.slice(2)+'ff',s=await createFinalizationSession({seeds:[seed(A,code,9n,1n,{[W(0)]:W(42)}),seed(B,'0x',3n,0n)]}),q=request('old',A),r=await run(s,q,0);
 assert.equal(r.post[A].exists,true);assert.equal(r.post[A].code,code);assert.equal(r.post[A].nonce,'1');assert.equal(r.post[A].balance,'0');assert.equal(r.post[A].persistent[W(0)],W(42));assert.equal(r.post[B].balance,'12');
 assert.deepEqual(r.finalization.eligible,[]);assert.deepEqual(r.finalization.retained,[{address:A,beneficiary:B}]);
});
test('preexisting SELFDESTRUCT to self keeps nonzero balance',async()=>{
 const code='0x30ff',s=await createFinalizationSession({seeds:[seed(A,code,9n,1n,{[W(0)]:W(42)})]}),q=request('self',A),r=await run(s,q,0);
 assert.equal(r.post[A].balance,'9');assert.equal(r.post[A].nonce,'1');assert.equal(r.post[A].code,code);assert.equal(r.post[A].persistent[W(0)],W(42));assert.deepEqual(r.finalization.deletedAccounts,[]);
});
test('top-level created SELFDESTRUCT actually clears metadata/code/storage at end',async()=>{
 const born=createContractAddress(createAddressFromString(CALLER),0n).toString();const code='0x602a5f5560115f5d73'+B.slice(2)+'ff';
 const s=await createFinalizationSession({seeds:[seed(B,'0x',3n,0n)],watch:[{address:born,persistent:[W(0)],transient:[W(0)]}]}),q={id:'new-die',kind:'create',data:code,value:5n},r=await run(s,q,0);
 assert.equal(r.message.createdAddress,born);assert.equal(r.messagePost[born].exists,true);assert.equal(r.messagePost[born].persistent[W(0)],W(42));assert.equal(r.post[born].exists,false);assert.equal(r.post[born].nonce,null);assert.equal(r.post[born].code,'0x');assert.equal(r.post[born].persistent[W(0)],W(0));assert.equal(r.post[born].transient[W(0)],W(0));assert.equal(r.post[B].balance,'8');assert.equal(r.post[CALLER].balance,(M-5n).toString());
 assert.deepEqual(r.finalization.eligible,[{address:born,beneficiary:B}]);assert.ok(r.operations.some(o=>o.kind==='transient.put'&&o.value==='0x11'));assert.deepEqual(r.finalization.deletedAccounts,[born]);
});
test('same-transaction creation SELFDESTRUCT-to-self burns then deletes',async()=>{
 const born=createContractAddress(createAddressFromString(CALLER),0n).toString(),s=await createFinalizationSession(),q={id:'born-self',kind:'create',data:'0x30ff',value:5n},r=await run(s,q,0);
 assert.equal(r.message.createdAddress,born);assert.equal(r.messagePost[born].balance,'0');assert.equal(r.post[born].exists,false);assert.equal(r.post[CALLER].balance,(M-5n).toString());
});
test('root REVERT keeps exact full bytes and actual nonce without retaining value/storage writes',async()=>{
 const code='0x602a5f5563deadbeef5f526004601cfd',s=await createFinalizationSession({seeds:[seed(A,code,9n,1n,{[W(0)]:W(7)})]}),q=request('revert',A,'0x',5n),r=await run(s,q,0);
 assert.equal(r.message.exception,'revert');assert.equal(r.message.bytes,'0xdeadbeef');assert.equal(r.post[CALLER].nonce,'1');assert.equal(r.post[CALLER].balance,M.toString());assert.equal(r.post[A].balance,'9');assert.equal(r.post[A].persistent[W(0)],W(7));assert.deepEqual(r.message.createdAddresses,[]);assert.deepEqual(r.message.selfdestruct,[]);assert.deepEqual(r.message.logs,[]);
 assert.equal(r.frames[0].memory.status,'captured');assert.ok(r.frames[0].memory.bytes.endsWith('deadbeef'));
});
test('EIP161 touched-empty cleanup normalizes actual account/code/storage absence',async()=>{
 const code='0x5f5f5f5f5f73'+EMPTY.slice(2)+'61c350f15000',s=await createFinalizationSession({seeds:[seed(A,code),seed(EMPTY,'0x',0n,0n)]}),q=request('empty',A),r=await run(s,q,0);
 assert.equal(r.messagePost[EMPTY].exists,true);assert.equal(r.post[EMPTY].exists,false);assert.equal(r.post[EMPTY].code,'0x');assert.deepEqual(r.finalization.deletedAccounts,[EMPTY]);assert.ok(r.finalization.actions.some(a=>a.kind==='delete'&&a.reason==='eip161'&&a.address===EMPTY));
});
test('missing committed root evidence never becomes an empty success receipt',async()=>{
 const s=await createFinalizationSession({seeds:[seed(EMPTY,'0x',1n,0n)]});await assert.rejects(s.execute(request('empty-root',EMPTY)),e=>e instanceof Host1Blocked&&/missing committed root Map\/Set/.test(e.message));await assert.rejects(s.snapshot(),Host1Blocked);
});
for(const [name,value]of [['bad bytes','0x1'],['bad address','0x01'],['bad word','0x00']])test(name,()=>assert.throws(()=>name==='bad bytes'?parseBytes(value):name==='bad address'?parseAddress(value):parseWord(value)));
test('runtime input refuses forged substate/custom gas/value/static-create rather than change budgets',async()=>{
 const s=await createFinalizationSession();for(const q of [{id:'x',kind:'create',to:A,data:'0x'},{id:'x',kind:'static',to:A,data:'0x',value:1n},{id:'x',kind:'call',to:A,data:'0x',selfdestruct:new Map()},{id:'x',kind:'call',to:A,data:'0x',gasLimit:1n}])await assert.rejects(s.execute(q));assert.equal((await s.snapshot())[CALLER].nonce,'0');
});

test('actual DELEGATECALL keeps code address distinct from storage owner and full returndata',async()=>{
 const target='0x602a5f55602a5f5260205ff3',wrapper='0x5f5f5f5f73'+B.slice(2)+'61c350f45000';const s=await createFinalizationSession({seeds:[seed(A,wrapper,1n),seed(B,target,1n)],watch:[{address:B,persistent:[W(0)],transient:[]}]}),q=request('delegate-owner',A),r=await run(s,q,0);
 assert.equal(r.frames.length,2);const child=r.frames[1];assert.equal(child.delegatecall,true);assert.equal(child.invocationOpcode,'DELEGATECALL');assert.equal(child.to,A);assert.equal(child.executionAddress,A);assert.equal(child.messageCodeAddress,B);assert.equal(child.codeAddress,B);assert.equal(child.caller,CALLER);assert.equal(r.post[A].persistent[W(0)],W(42));assert.equal(r.post[B].persistent[W(0)],W(0));assert.equal(r.frames[0].lastCallReturnData.bytes,W(42));
 const bad=structuredClone(r);bad.frames[1].executionAddress=B;assert.throws(()=>validateFinalizedMessage(bad,q,0));
 for(const mutate of [x=>{x.frames[1].invocationOpcode='CALLCODE';x.frames[1].delegatecall=false;},x=>x.frames[1].caller=A,x=>x.frames[1].value='1',x=>x.frames[1].static=true]){const bad=structuredClone(r);mutate(bad);assert.throws(()=>validateFinalizedMessage(bad,q,0));}

});

test('concurrent requests are refused while completed sessions keep ordered state',async()=>{
 const s=await createFinalizationSession({seeds:[seed(A,'0x602a5f5500')]}),q=request('first',A),running=s.execute(q);
 await assert.rejects(s.execute(request('overlap',A)),Host1Blocked);const r=await running;validateFinalizedMessage(r,q,0);
 const next=request('next',A),r2=await run(s,next,1);assert.equal(r2.pre[CALLER].nonce,'1');assert.equal(r2.post[CALLER].nonce,'2');assert.equal(r2.pre[A].persistent[W(0)],W(42));assert.equal(r2.post[A].persistent[W(0)],W(42));
});

test('unobserved accounts/slots stay unavailable rather than becoming zero',async()=>{
 const s=await createFinalizationSession({seeds:[seed(A,'0x602a5f5500')]}),q=request('domain-read',A),r=await run(s,q,0);
 assert.equal(readObservedSlot(r,'post',A,'persistent',W(0)),W(42));assert.equal(readObservedAccount(r,'post',A).exists,true);
 assert.throws(()=>readObservedAccount(r,'post',B),/unobserved/);assert.throws(()=>readObservedSlot(r,'post',A,'persistent',W(7)),/unobserved/);
});

test('actual STATICCALL parent convention preserves caller/value/static and refuses child writes',async()=>{
 const wrapper='0x5f5f5f5f73'+B.slice(2)+'61c350fa5000',s=await createFinalizationSession({seeds:[seed(A,wrapper,1n),seed(B,'0x602a5f5500',1n)],watch:[{address:B,persistent:[W(0)],transient:[]}]}),q=request('static-child',A),r=await run(s,q,0),f=r.frames[1];
 assert.equal(f.invocationOpcode,'STATICCALL');assert.equal(f.static,true);assert.equal(f.value,'0');assert.equal(f.caller,A);assert.equal(f.output.exception,'static state change');assert.equal(r.post[B].persistent[W(0)],W(0));
 for(const mutate of [x=>x.frames[1].static=false,x=>x.frames[1].value='1',x=>x.frames[1].caller=CALLER]){const bad=structuredClone(r);mutate(bad);assert.throws(()=>validateFinalizedMessage(bad,q,0));}
});
