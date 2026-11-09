// Injected scheduling/clock boundary; no native transport, rendered UI or proof claim.
'use strict';
const test=require('node:test'),assert=require('node:assert/strict'),{EventEmitter}=require('node:events'),{performance}=require('node:perf_hooks');
const {waitForServerVersion,versionNotification,versionTimeoutMs}=require('../src/startup.cjs');
function fixture(t){
 let now=100;const timers=[],cleared=[],peer=new EventEmitter(),handlers=new Map();
 peer.onNotification=(method,fn)=>{handlers.set(method,fn);return{dispose(){handlers.delete(method);}};};
 t.mock.method(performance,'now',()=>now);t.mock.method(global,'setTimeout',(fn,ms)=>{const timer={fn,ms};timers.push(timer);return timer;});t.mock.method(global,'clearTimeout',timer=>cleared.push(timer));
 const wait=waitForServerVersion(peer),initial={name:'Scheduling fixture',version:'9.9.9'},pending=wait.start(initial);
 assert.equal(timers.length,1);assert.equal(timers[0].ms,5000);assert.equal(versionTimeoutMs,5000);
 return{wait,pending,peer,handlers,timers,cleared,advance(ms){now+=ms;},notify(){handlers.get(versionNotification)?.({name:initial.name,version:'1.2.3'});}};
}
test('a notification cannot win after the original version deadline while its timer callback is overdue (injected scheduling)',async t=>{
 for(const delay of [5000,5001]){const f=fixture(t);try{f.advance(delay);f.notify();assert.deepEqual(await f.pending,{serverInfo:{name:'Scheduling fixture',version:'unknown'},source:'timeout'});assert.equal(f.wait.pending,false);assert.equal(f.handlers.has(versionNotification),false);assert.equal(f.peer.listenerCount('close'),0);assert.ok(f.cleared.includes(f.timers[0]));f.timers[0].fn();}finally{f.wait.dispose();t.mock.restoreAll();}}
});
test('a current version before the deadline still wins and a delayed callback cannot replace it (injected scheduling)',async t=>{
 const f=fixture(t);try{f.advance(4999);f.notify();assert.deepEqual(await f.pending,{serverInfo:{name:'Scheduling fixture',version:'1.2.3'},source:'notification'});f.advance(2);f.timers[0].fn();assert.equal(f.wait.pending,false);assert.equal(f.handlers.has(versionNotification),false);}finally{f.wait.dispose();}
});
