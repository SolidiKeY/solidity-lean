import test from 'node:test';
import assert from 'node:assert/strict';
import {createFinalizationSession,Host1Blocked} from './index.mjs';
const A='0x'+'00'.repeat(18)+'0abc';
test('original five-million instruction budget is host-blocked, never an EVM failure receipt',async()=>{
 const s=await createFinalizationSession({seeds:[{address:A,nonce:1n,balance:1n,code:'0x5b600056',storage:{}}]});
 await assert.rejects(s.execute({id:'original-step-limit',kind:'call',to:A,data:'0x'}),e=>e instanceof Host1Blocked&&e.message.includes('reference instruction budget exhausted'));
 await assert.rejects(s.execute({id:'after-host-block',kind:'call',to:A,data:'0x'}),e=>e instanceof Host1Blocked&&e.message.includes('poisoned'));
});
