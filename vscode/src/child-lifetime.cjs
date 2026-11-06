// Closure confirmation is lifecycle evidence, never verifier/proof readiness.
'use strict';
const {terminateTree}=require('./backend.cjs');
const {processState,groupMembers,running}=require('./process-state.cjs');
const closures=new WeakMap();
function trackChild(child){child.processBirth??=processState(child.pid)?.birth;let closed=closures.get(child);if(!closed){closed=new Promise(resolve=>child.once('close',resolve));closures.set(child,closed);}return closed;}
async function waitForGroup(child,{deadline=Date.now()+1000,kill=false}={}){
 if(kill)terminateTree(child);
 if(groupMembers(child).some(running))terminateTree(child);
 while(groupMembers(child).some(running)){if(Date.now()>=deadline)throw new Error('Owned session remained live after shutdown deadline');await new Promise(setImmediate);}
}
async function waitForClose(child,{closed=trackChild(child),kill=false,timeoutMs=1000,deadline=Date.now()+timeoutMs}={}){
 if(kill&&(child.ownedGroup||child.pid&&child.exitCode===null&&child.signalCode===null))terminateTree(child);
 let timer;try{await Promise.race([closed,new Promise((resolve,reject)=>{timer=setTimeout(()=>reject(new Error('Owned child closure was not confirmed before shutdown deadline')),Math.max(0,deadline-Date.now()));})]);await waitForGroup(child,{deadline});}finally{clearTimeout(timer);}
}
module.exports={trackChild,waitForClose,waitForGroup};
