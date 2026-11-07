/** Guarded regression: wrong-fork/format and negative-block inputs cannot be admitted by bypassing real header validation. */
import test from 'node:test';import assert from 'node:assert/strict';
import {executeBlockchain,transactionObservations} from '../../../../scripts/h62/item3/g52-differential/blockchain_adapter.mjs';
test('unsupported fixture domains refuse before a provider can be fabricated',async()=>{
 for(const f of [{network:'Prague'},{network:'Osaka',_info:{'fixture-format':'blockchain_test_engine'}},{network:'Osaka',_info:{'fixture-format':'blockchain_test'},sealEngine:'unknown'}])assert.equal((await executeBlockchain({fixture:f},{},{})).status,'unsupported');
});
test('missing block bytes refuse before execution',async()=>{
 const fixture={network:'Osaka',_info:{'fixture-format':'blockchain_test'},sealEngine:'NoProof',blocks:[{expectException:'invalid-header'}]};
 const result=await executeBlockchain({fixture},{},{});assert.equal(result.status,'unsupported');assert.equal(result.reason,'missing-block-rlp');
});

test('missing native transaction output or inconsistent receipt cannot be serialized as an observation',()=>{
 const block={transactions:[{hash:()=>new Uint8Array(),type:0,gasLimit:30n}]};
 const bytes=x=>'0x'+Buffer.from(x).toString('hex');
 assert.throws(()=>transactionObservations(block,{results:[],receipts:[]},bytes),/incomplete/);
 const r={execResult:{returnValue:new Uint8Array([1]),executionGasUsed:2n,logs:[]},totalGasSpent:3n,gasRefund:0n};
 assert.throws(()=>transactionObservations(block,{results:[r],receipts:[{status:0,logs:[],cumulativeBlockGasUsed:3n}]},bytes),/disagreement/);
 r.execResult.returnValue=undefined;
 assert.throws(()=>transactionObservations(block,{results:[r],receipts:[{}]},bytes),/missing/);
});
