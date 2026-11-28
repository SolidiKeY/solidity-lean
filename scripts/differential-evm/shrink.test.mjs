import {test} from 'node:test';
import assert from 'node:assert/strict';
import {shrink} from './shrink.mjs';
test('delta debugging removes irrelevant instructions',async()=>{const r={instructions:[{op:'PUSH',value:'7'},{op:'NOT'},{op:'POP'},{op:'STOP'}]};const result=await shrink(r,async c=>c.instructions.some(i=>i.op==='NOT')?'mismatch':'agree');assert.deepEqual(result.record.instructions,[{op:'NOT'}]);assert.equal(r.instructions.length,4);});
test('blocked candidates cannot shrink',async()=>{const r={instructions:[{op:'NOT'},{op:'STOP'}]};assert.deepEqual((await shrink(r,async c=>c.instructions.length===2?'mismatch':'blocked')).record,r);});
test('initial mismatch is required',async()=>{await assert.rejects(()=>shrink({instructions:[]},async()=> 'agree'));});
