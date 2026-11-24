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
test('post-disposal readback and file removal wait until every disposal settles (injected)',async()=>{
 let release,started=false,allSettled=false;const barrier=new Promise(r=>release=r),during=[],removed=[];
 const resources=[{name:'fast',f:{directory:'fast'},client:{get child(){if(started&&!allSettled)during.push('fast');return null;},dispose:async()=>{started=true;}}},{name:'slow',f:{directory:'slow'},client:{get child(){if(started&&!allSettled)during.push('slow');return null;},dispose:async()=>{started=true;await barrier;allSettled=true;}}}];
 const pending=settleFixtures(resources,{remove:path=>removed.push(path)});await new Promise(setImmediate);const beforeRelease={during:during.slice(),removed:removed.slice()};release();const rows=await pending;assert.deepEqual(beforeRelease.during,[]);assert.deepEqual(beforeRelease.removed,[]);
 assert.deepEqual(rows.map(r=>r.status),['fulfilled','fulfilled']);assert.deepEqual(removed,['fast','slow']);assert.ok(rows.every(r=>r.afterBarrier==='all-disposals-settled'&&r.disposalSettled<=r.afterReadStarted&&r.afterReadStarted<=r.settled));
});
test('removal failure after the barrier cannot abandon later readbacks or removals (injected)',async()=>{
 const failure=Error('injected removal failure'),attempted=[],removed=[];let recorded;
 const resources=['first','second'].map(name=>({name,f:{directory:name},client:{dispose:async()=>attempted.push(name)}}));
 await assert.rejects(settleFixtures(resources,{remove:path=>{removed.push(path);if(path==='first')throw failure;},record:rows=>recorded=rows}),e=>e instanceof AggregateError&&e.errors.includes(failure));assert.deepEqual(attempted,['first','second']);assert.deepEqual(removed,['first','second']);assert.deepEqual(recorded.map(r=>r.status),['rejected','fulfilled']);
});

test('falsy or unprintable readback failures cannot abandon cleanup or delete unconfirmed fixtures (injected)',async()=>{
 let diagnosticReads=0;
 for(const reason of [null,false,0,'',undefined,Object.freeze(Error('')),Object.defineProperty({},'message',{get(){diagnosticReads++;throw Error('hostile diagnostic accessor');}})]){const attempted=[],removed=[],resources=[{name:'failed-readback',f:{directory:'keep'},client:{get child(){throw reason;},dispose:async()=>attempted.push('keep')}},{name:'other',f:{directory:'other'},client:{dispose:async()=>attempted.push('other')}}];let recorded;
  await assert.rejects(settleFixtures(resources,{remove:path=>removed.push(path),record:rows=>recorded=rows}),e=>e instanceof AggregateError&&e.errors.includes(reason));assert.deepEqual(attempted,['keep','other']);assert.deepEqual(removed,['other']);assert.ok(Object.hasOwn(recorded[0].before,'readbackError'));assert.ok(Object.hasOwn(recorded[0].after,'readbackError'));
 }
 assert.equal(diagnosticReads,0);
});
