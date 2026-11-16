/** Guarded regression: negative payload labels, RPC failures, missing native
 * rejection/prefix evidence and conversion errors must never earn match credit.
 * Synthetic constructors below exercise adapter contracts, not EVM semantics.
 */
import test from 'node:test';
import assert from 'node:assert/strict';
import {rejectionPlan,convertExpectedInvalidEngineFixture,executeExpectedInvalidEngineFixture,rejectionExitCode} from '../../../../scripts/h62/item3/g52-differential/engine_rejection_reference.mjs';
const h=n=>'0x'+n.toString(16).padStart(64,'0');
const expected='BlockException.INCORRECT_EXCESS_BLOB_GAS';
const request=(n,negative=false)=>({newPayloadVersion:4,forkchoiceUpdatedVersion:3,params:[{blockHash:h(n),stateRoot:h(9)},[],h(0),[]],...(negative?{validationError:expected}:{})});
const record=()=>({fixture:{network:'Osaka',_info:{'fixture-format':'blockchain_test_engine'},pre:{},postState:{},genesisBlockHeader:{hash:h(0),stateRoot:h(9)},engineNewPayloads:[request(1),request(2,true)]}});
const block=value=>({hash:()=>value,serialize:()=>value,transactions:[]});
const m={Common:class {},Mainnet:{},Hardfork:{Osaka:'osaka'},bytesToHex:x=>x,hexToBytes:x=>Buffer.from(x.slice(2),'hex'),createBlock:()=>block(h(0)),createBlockFromExecutionPayload:async p=>block(p.blockHash)};
const native=()=>({status:'reference_match',blocks:[{hash:h(1),state_root:h(9)}],rejections:[{status:'reference_match',block_index:1,expected_exception:expected,engine_reason:'expected blob gas: 0, got: 1',validation_facts:{stage:'provider-validation'},before_state_root:h(9),after_state_root:h(9),before_head:h(1),after_head:h(1)}]});

test('negative plan preserves input and exact alternative categories',async()=>{
 const input=record(),original=structuredClone(input);input.fixture.engineNewPayloads[1].validationError+='|BlockException.INCORRECT_BLOB_GAS_USED';
 const saved=structuredClone(input),plan=rejectionPlan(input);
 assert.equal(plan.status,'planned');assert.deepEqual(input,saved);
 assert.equal(plan.expected[0].expected_exception,input.fixture.engineNewPayloads[1].validationError);
 assert.equal(Object.hasOwn(plan.record.fixture.engineNewPayloads[1],'validationError'),false);
 const converted=await convertExpectedInvalidEngineFixture(original,m);
 assert.equal(converted.record.fixture.blocks[1].expectException,expected);
 assert.equal(Object.hasOwn(converted.record.fixture.blocks[0],'expectException'),false);
});

test('RPC exceptions, malformed categories, unknown fields and positive sequences refuse before execution',async()=>{
 for(const mutate of [r=>r.fixture.engineNewPayloads[1].errorCode='-32602',r=>r.fixture.engineNewPayloads[1].validationError='',r=>r.fixture.engineNewPayloads[1].validationError=['BlockException.INVALID_REQUESTS'],r=>r.fixture.engineNewPayloads[1].unexpected=true,r=>delete r.fixture.engineNewPayloads[1].validationError]) {
  const r=record();mutate(r);let calls=0;
  const out=await executeExpectedInvalidEngineFixture(r,m,async()=>{calls++;return native();});assert.equal(out.status,'unsupported');assert.equal(calls,0);assert.equal(rejectionExitCode({unsupported:1}),2);
 }
});

test('native rejection is separate and incomplete even with complete rollback/prefix evidence',async()=>{
 const out=await executeExpectedInvalidEngineFixture(record(),m,async converted=>{assert.equal(converted.fixture.blocks[1].expectException,expected);return native();});
 assert.equal(out.status,'payload_rejection_reference_match');assert.equal(out.engine_rpc_complete,false);assert.equal(out.differential_complete,false);assert.equal(out.source_semantics,'unsupported-adapter-pending');assert.equal(rejectionExitCode({[out.status]:1}),2);
});

test('forged rejection categories, rollback, head, indices and omitted prefix cannot pass',async()=>{
 for(const mutate of [n=>n.rejections=[],n=>n.blocks=[],n=>n.blocks[0].hash=h(7),n=>n.rejections[0].after_state_root=h(8),n=>n.rejections[0].after_head=h(8),n=>n.rejections[0].before_head='',n=>n.rejections[0].block_index=0,n=>n.rejections[0].expected_exception='BlockException.INVALID_REQUESTS',n=>n.rejections[0].engine_reason='unrecognized native failure']) {
  const n=native();mutate(n);const out=await executeExpectedInvalidEngineFixture(record(),m,async()=>n);assert.equal(out.status,'engine_error',JSON.stringify(n));assert.equal(rejectionExitCode({[out.status]:1}),1);
 }
});

test('wrong native category and expected-invalid acceptance remain mismatches',async()=>{
 const n={status:'reference_mismatch',fields:['block_admission']};const out=await executeExpectedInvalidEngineFixture(record(),m,async()=>n);
 assert.equal(out.status,'payload_rejection_mismatch');assert.equal(rejectionExitCode({[out.status]:1}),1);
});

test('worker failures, unsupported native outcomes and conversion exceptions fail, never downgrade',async()=>{
 for(const n of [undefined,{status:'engine_error',retryable:true,reason:'native-worker-timeout'},{status:'engine_error',retryable:true,reason:'native-worker-exited'},{status:'unsupported',reason:'unclassified-block-rejection'}]) {
  const out=await executeExpectedInvalidEngineFixture(record(),m,async()=>n);assert.equal(out.status,'engine_error');assert.equal(out.retryable,true);assert.equal(rejectionExitCode({[out.status]:1}),1);
 }
 const bad={...m,createBlockFromExecutionPayload:async()=>{throw new Error('invalid blockHash');}};
 const out=await executeExpectedInvalidEngineFixture(record(),bad,async()=>{throw new Error('must not execute');});assert.equal(out.status,'engine_error');assert.match(out.error,/invalid blockHash/);
});

test('equal but unrelated rollback head/root and wrong accepted root cannot pass',async()=>{
 for(const mutate of [n=>{n.rejections[0].before_head=h(7);n.rejections[0].after_head=h(7);},n=>{n.rejections[0].before_state_root=h(7);n.rejections[0].after_state_root=h(7);},n=>n.blocks[0].state_root=h(7)]) {
  const n=native();mutate(n);const out=await executeExpectedInvalidEngineFixture(record(),m,async()=>n);assert.equal(out.status,'engine_error');assert.equal(rejectionExitCode({[out.status]:1}),1);
 }
});

test('genesis and consecutive rejections retain the same committed prefix',async()=>{
 const r=record();r.fixture.engineNewPayloads=[request(2,true),request(3,true)];
 const n=native();n.blocks=[];n.rejections=[0,1].map(index=>({...structuredClone(native().rejections[0]),block_index:index,before_head:h(0),after_head:h(0)}));
 assert.equal((await executeExpectedInvalidEngineFixture(r,m,async()=>n)).status,'payload_rejection_reference_match');
 n.rejections[1].before_head=h(2);n.rejections[1].after_head=h(2);
 assert.equal((await executeExpectedInvalidEngineFixture(r,m,async()=>n)).status,'engine_error');
});
