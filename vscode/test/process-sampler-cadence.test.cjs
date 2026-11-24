// Injected timer/scan controls only; no native resource or performance claim.
'use strict';
const test=require('node:test'),assert=require('node:assert/strict'),{ProcessSampler}=require('../parity/core.cjs');
test('a slow initial scan cannot postpone the first interval by another full period',t=>{
 let clock=0,due,callback,calls=0,cleared=0;const timer={unref(){}};
 t.mock.method(global,'setInterval',(fn,interval)=>{assert.equal(interval,100);due=clock+interval;callback=fn;return timer;});t.mock.method(global,'clearInterval',value=>{assert.equal(value,timer);cleared++;});
 t.mock.method(ProcessSampler.prototype,'sample',()=>{calls++;clock+=calls===1?250:5;});
 const sampler=new ProcessSampler(123,100);try{assert.equal(calls,1);assert.ok(due<=clock,'original interval must already be due after the long initial scan');callback();assert.equal(calls,2);}finally{sampler.stop();}assert.equal(cleared,1);
});
test('initial sampling failure retains its rejection identity without leaving a timer',t=>{
 const active=new Set();t.mock.method(global,'setInterval',()=>{const timer={unref(){}};active.add(timer);return timer;});t.mock.method(global,'clearInterval',timer=>active.delete(timer));
 for(const reason of [null,Object.freeze(Error('initial scan failed'))]){t.mock.method(ProcessSampler.prototype,'sample',()=>{throw reason;});assert.throws(()=>new ProcessSampler(123,100),error=>error===reason);assert.equal(active.size,0);}
});
