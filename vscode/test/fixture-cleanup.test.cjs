// Regression: failed fixture disposal must not abandon other admitted cleanup or receipts.
'use strict';
const test=require('node:test'),assert=require('node:assert/strict'),{settleFixtures}=require('./fixture-cleanup.cjs');
test('one rejected disposal still waits for every admitted fixture and retains every outcome (injected)',async()=>{
 const calls=[],failure=Error('injected confirmed-close failure');let release,recorded,settled=false;const slow=new Promise(resolve=>{release=resolve;}),resources=[{name:'failed',f:{directory:'failed-path'},client:{dispose:async()=>{calls.push('failed');throw failure;}}},{name:'slow',f:{directory:'slow-path'},client:{dispose:async()=>{calls.push('slow');await slow;}}}];
 const pending=settleFixtures(resources,{remove:path=>calls.push('removed:'+path),record:rows=>{recorded=rows;}}).catch(error=>{settled=true;return error;});await new Promise(setImmediate);assert.deepEqual(calls,['failed','slow']);assert.equal(settled,false);release();const error=await pending;assert.ok(error instanceof AggregateError);assert.deepEqual(error.errors,[failure]);assert.equal(error.cleanup,recorded);assert.deepEqual(recorded.map(row=>row.status),['rejected','fulfilled']);assert.deepEqual(calls,['failed','slow','removed:slow-path']);assert.equal(recorded[0].directory,'failed-path');
});
test('receipt failure is not silently accepted after all disposals were attempted (injected)',async()=>{
 const failure=Error('injected receipt failure');let disposed=false;await assert.rejects(settleFixtures([{f:{directory:'injected'},client:{dispose:async()=>{disposed=true;}}}],{remove:()=>{},record:()=>{throw failure;}}),e=>e instanceof AggregateError&&e.errors.includes(failure));assert.equal(disposed,true);
});

test('readback failure cannot prevent another fixture cleanup or become a successful receipt (injected)',async()=>{
 const failure=Error('injected ownership readback failure'),attempted=[],removed=[];const resources=[{name:'readback',f:{directory:'first'},client:{get child(){throw failure;},dispose:async()=>{attempted.push('first');}}},{name:'other',f:{directory:'other'},client:{dispose:async()=>{attempted.push('other');}}}];let recorded;
 await assert.rejects(settleFixtures(resources,{remove:path=>removed.push(path),record:rows=>{recorded=rows;}}),e=>e instanceof AggregateError&&e.errors.includes(failure));assert.deepEqual(attempted,['first','other']);assert.equal(recorded[0].before.readbackError,failure.message);assert.equal(recorded[0].after.readbackError,failure.message);assert.deepEqual(recorded.map(row=>row.status),['fulfilled','fulfilled']);assert.deepEqual(removed,['other'],'unconfirmed readback fixture remains available');
});
