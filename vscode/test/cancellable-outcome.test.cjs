// Injected Promise/signal lifecycle controls only; no native or proof claim.
'use strict';
const test=require('node:test'),assert=require('node:assert/strict'),{getEventListeners}=require('node:events'),{cancellable}=require('../src/rpc.cjs');
for(const [name,reason]of [['null',null],['false',false],['zero',0],['empty',''],['undefined',undefined],['frozen Error',Object.freeze(Error('original failure'))]]){
 test('signal wrapper preserves rejected '+name+' as rejection with original identity',async()=>{
  const controller=new AbortController(),pending=cancellable(Promise.reject(reason),controller.signal);assert.equal(getEventListeners(controller.signal,'abort').length,1);
  const actual=await pending.then(value=>({state:'fulfilled',value}),value=>({state:'rejected',value}));assert.equal(actual.state,'rejected');assert.equal(actual.value,reason);assert.equal(getEventListeners(controller.signal,'abort').length,0);
 });
}
test('falsy successful values remain successful and the no-signal path retains promise identity',async()=>{
 for(const value of [null,false,0,'',undefined]){const source=Promise.resolve(value),controller=new AbortController();assert.equal(cancellable(source),source);assert.equal(await cancellable(source,controller.signal),value);assert.equal(getEventListeners(controller.signal,'abort').length,0);}
});
test('one cancelled startup waiter does not cancel a shared promise or another waiter',async()=>{
 let resolve;const source=new Promise(r=>resolve=r),a=new AbortController(),b=new AbortController(),first=cancellable(source,a.signal),second=cancellable(source,b.signal),rejected=assert.rejects(first,e=>e.code===-32800);a.abort();await rejected;assert.equal(getEventListeners(a.signal,'abort').length,0);assert.equal(getEventListeners(b.signal,'abort').length,1);
 resolve('ready');assert.equal(await second,'ready');assert.equal(getEventListeners(b.signal,'abort').length,0);
});
test('abort followed by late source rejection settles and removes its listener only once',async t=>{
 let reject;const source=new Promise((_,r)=>reject=r),controller=new AbortController(),remove=controller.signal.removeEventListener.bind(controller.signal);let removes=0;t.mock.method(controller.signal,'removeEventListener',(...args)=>{removes++;return remove(...args);});
 const pending=cancellable(source,controller.signal),rejected=assert.rejects(pending,e=>e.code===-32800);controller.abort();await rejected;reject(Object.freeze(Error('late failure')));await new Promise(setImmediate);assert.equal(removes,1);assert.equal(getEventListeners(controller.signal,'abort').length,0);
});

test('already aborted signal retains cancellation priority and handles a rejected source',async()=>{
 for(const source of [Promise.resolve('ready'),Promise.reject(null)]){const controller=new AbortController();controller.abort();await assert.rejects(cancellable(source,controller.signal),e=>e.code===-32800);assert.equal(getEventListeners(controller.signal,'abort').length,0);}
});
