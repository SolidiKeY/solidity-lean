// Closure confirmation is lifecycle evidence, never verifier/proof readiness.
'use strict';
const {terminateTree}=require('./backend.cjs');
const {processState,groupMembers,running}=require('./process-state.cjs');
const closures=new WeakMap();
function trackChild(child){child.processBirth??=processState(child.pid)?.birth;let closed=closures.get(child);if(!closed){closed=new Promise(resolve=>child.once('close',resolve));closures.set(child,closed);}return closed;}
async function waitForGroup(child,{deadline=Date.now()+1000,kill=false}={}){
 if(kill)terminateTree(child);
 let members=groupMembers(child);
 if(members.some(running)){terminateTree(child);members=groupMembers(child);}
 while(members.some(running)){if(Date.now()>=deadline)throw new Error('Owned session remained live after shutdown deadline');await new Promise(setImmediate);members=groupMembers(child);}
}
async function waitForClose(child,{closed=trackChild(child),kill=false,timeoutMs=1000,deadline=Date.now()+timeoutMs}={}){
 if(kill&&(child.ownedGroup||child.pid&&child.exitCode===null&&child.signalCode===null))terminateTree(child);
 // A private-session descendant may retain stdio after its root exits. Retire
 // that owned group before waiting for pipe closure, never treating exit as close.
 let timer,onExit;
 const exitFailure=new Promise((resolve,reject)=>{if(!child.ownedGroup)return;onExit=()=>{try{if(groupMembers(child).some(running))terminateTree(child);}catch(error){reject(error);}};if(child.exitCode!=null||child.signalCode!=null)onExit();else child.once('exit',onExit);});
 try{await Promise.race([closed,exitFailure,new Promise((resolve,reject)=>{timer=setTimeout(()=>reject(new Error('Owned child closure was not confirmed before shutdown deadline')),Math.max(0,deadline-Date.now()));})]);await waitForGroup(child,{deadline});}finally{clearTimeout(timer);if(onExit)child.removeListener('exit',onExit);}
}
module.exports={trackChild,waitForClose,waitForGroup};
