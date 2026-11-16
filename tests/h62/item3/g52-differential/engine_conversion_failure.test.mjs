/** Guarded regression: a constructor error must keep its exact payload index
 * and original parameter commitment while remaining a failed, retryable job.
 * Synthetic SDK callbacks test diagnostics only; no native or Source credit.
 */
import test from 'node:test';
import assert from 'node:assert/strict';
import {createHash} from 'node:crypto';
import {convertEngineFixture,engineConversionFailure,executeEngineFixture,engineExitCode} from '../../../../scripts/h62/item3/g52-differential/engine_payload_reference.mjs';
import {executeExpectedInvalidEngineFixture,rejectionExitCode} from '../../../../scripts/h62/item3/g52-differential/engine_rejection_reference.mjs';
const h=n=>'0x'+n.toString(16).padStart(64,'0');
const block=x=>({hash:()=>x,serialize:()=>x,transactions:[]});
const request=n=>({newPayloadVersion:4,forkchoiceUpdatedVersion:3,params:[{blockHash:h(n),transactions:['0x04c0']},[],h(0),[]]});
const record=()=>({fixture:{network:'Osaka',_info:{'fixture-format':'blockchain_test_engine'},pre:{},postState:{},genesisBlockHeader:{hash:h(0)},engineNewPayloads:[request(1),request(2)]}});
const m={Common:class {},Mainnet:{},Hardfork:{Osaka:'osaka'},bytesToHex:x=>x,hexToBytes:x=>Buffer.from(x.slice(2),'hex'),createBlock:()=>block(h(0)),createBlockFromExecutionPayload:async p=>block(p.blockHash)};
const digest=x=>createHash('sha256').update(JSON.stringify(x)).digest('hex');

test('both SDK string and Error failures retain exact constructor position and input commitment',async()=>{
 for(const failure of ['Invalid tx at index 0: gas cap',new Error('bad blockHash')]) {
  const r=record(),saved=structuredClone(r),sha=digest(r.fixture.engineNewPayloads[1].params);
  const sdk={...m,createBlockFromExecutionPayload:async p=>{if(p.blockHash===h(2))throw failure;return block(p.blockHash);}};
  let caught;try{await convertEngineFixture(r,sdk);}catch(e){caught=e;}
  const facts=engineConversionFailure(caught);
  assert.deepEqual(facts,{stage:'execution-payload-construction',payload_index:1,parameter_encoding:'JSON.stringify(params)',parameters_sha256:sha,sdk_diagnostic:String(failure),native_execution_evidence:false});
  facts.payload_index=0;assert.equal(engineConversionFailure(caught).payload_index,1);assert.deepEqual(r,saved);
 }
});

test('ordinary and expected-invalid paths keep failure status, exit and no worker calls',async()=>{
 for(const negative of [false,true]) {
  const r=record();if(negative)r.fixture.engineNewPayloads[1].validationError='TransactionException.GAS_LIMIT_EXCEEDS_MAXIMUM';
  const sdk={...m,createBlockFromExecutionPayload:async()=>{throw 'Invalid tx at index 0: gas cap';}};
  let calls=0;const worker=async()=>{calls++;throw new Error('must not execute');};
  const result=await (negative?executeExpectedInvalidEngineFixture:executeEngineFixture)(r,sdk,worker);
  assert.equal(result.status,'engine_error');assert.equal(result.retryable,true);assert.equal(calls,0);
  assert.equal(result.conversion_failure.payload_index,0);assert.equal(result.conversion_failure.native_execution_evidence,false);
  assert.equal((negative?rejectionExitCode:engineExitCode)({engine_error:1}),1);
 }
});

test('parameter commitment precedes constructor mutation and arbitrary error properties cannot forge provenance',async()=>{
 const r=record(),sha=digest(r.fixture.engineNewPayloads[0].params);
 const sdk={...m,createBlockFromExecutionPayload:async()=>{r.fixture.engineNewPayloads[0].params[0].transactions=[];throw 'failure';}};
 const result=await executeEngineFixture(r,sdk,async()=>{throw 'must not execute';});
 assert.equal(result.conversion_failure.parameters_sha256,sha);
 const forged=new Error('outside constructor');forged.conversion_failure=result.conversion_failure;
 assert.equal(engineConversionFailure(forged),undefined);
 const badGenesis={...m,createBlock:()=>{throw forged;}};
 const outside=await executeEngineFixture(record(),badGenesis,async()=>{});
 assert.equal(outside.status,'engine_error');assert.equal(Object.hasOwn(outside,'conversion_failure'),false);
});

test('worker results cannot promote reserved constructor provenance',async()=>{
 const forged={stage:'execution-payload-construction',payload_index:999,parameters_sha256:'f'.repeat(64)};
 for(const status of ['engine_error','unsupported','reference_match','reference_mismatch']) {
  const result=await executeEngineFixture(record(),m,async()=>({status,conversion_failure:forged}));
  assert.equal(Object.hasOwn(result,'conversion_failure'),false);
  assert.equal(result.status,{engine_error:'engine_error',unsupported:'engine_error',reference_match:'payload_reference_match',reference_mismatch:'payload_reference_mismatch'}[status]);
 }
});
