/** Guarded regression: wrong-fork/format and negative-block inputs cannot be admitted by bypassing real header validation. */
import test from 'node:test';import assert from 'node:assert/strict';
import {executeBlockchain} from '../../../../scripts/h62/item3/g52-differential/blockchain_adapter.mjs';
test('unsupported fixture domains refuse before a provider can be fabricated',async()=>{
 for(const f of [{network:'Prague'},{network:'Osaka',_info:{'fixture-format':'blockchain_test_engine'}},{network:'Osaka',_info:{'fixture-format':'blockchain_test'},sealEngine:'unknown'}])assert.equal((await executeBlockchain({fixture:f},{},{})).status,'unsupported');
});
test('expected-invalid blocks never count as positive execution',async()=>{
 const fixture={network:'Osaka',_info:{'fixture-format':'blockchain_test'},sealEngine:'NoProof',blocks:[{rlp:'0x',expectException:'invalid-header'}]};
 const result=await executeBlockchain({fixture},{},{});assert.equal(result.status,'unsupported');assert.equal(result.reason,'expected-block-rejection-adapter-pending');
});
