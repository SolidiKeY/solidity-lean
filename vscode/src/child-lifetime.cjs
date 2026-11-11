// Closure confirmation is lifecycle evidence, never verifier/proof readiness.
'use strict';
const {terminateTree}=require('./backend.cjs');
const {processState,groupMembers,running}=require('./process-state.cjs');
const closures=new WeakMap();
function trackChild(child){child.processBirth??=processState(child.pid)?.birth;let closed=closures.get(child);if(!closed){closed=new Promise(resolve=>child.once('close',resolve));closures.set(child,closed);}return closed;}
async function waitForGroup(child,{deadline=Date.now()+1000,kill=false}={}){
 const started=Date.now();
 if(kill)terminateTree(child);
 let members=groupMembers(child);
 if(members.some(running)){terminateTree(child);members=groupMembers(child);}
 while(members.some(running)){if(Date.now()>=deadline)throw new Error('Owned session remained live after shutdown deadline: '+describe(child,started));await new Promise(setImmediate);members=groupMembers(child);}
}
async function waitForClose(child,{closed=trackChild(child),kill=false,timeoutMs=1000,deadline=Date.now()+timeoutMs}={}){
 const started=Date.now();
 if(kill&&(child.ownedGroup||child.pid&&child.exitCode===null&&child.signalCode===null))terminateTree(child);
 // A private-session descendant may retain stdio after its root exits. Retire
 // that owned group before waiting for pipe closure, never treating exit as close.
 let timer,onExit;
 const exitFailure=new Promise((resolve,reject)=>{if(!child.ownedGroup)return;onExit=()=>{try{if(groupMembers(child).some(running))terminateTree(child);}catch(error){reject(error);}};if(child.exitCode!=null||child.signalCode!=null)onExit();else child.once('exit',onExit);});
 try{await Promise.race([closed,exitFailure,new Promise((resolve,reject)=>{timer=setTimeout(()=>reject(new Error('Owned child closure was not confirmed before shutdown deadline: '+describe(child,started))),Math.max(0,deadline-Date.now()));})]);await waitForGroup(child,{deadline});}finally{clearTimeout(timer);if(onExit)child.removeListener('exit',onExit);}
}
// Shutdown-timeout diagnostics only (no effect on deadlines or decisions): name
// the child and list its live descendants so a CI failure says what held it.
function command(pid){try{return require('node:fs').readFileSync('/proc/'+pid+'/cmdline','utf8').split('\0').filter(Boolean).map(a=>a.length>60?a.slice(0,57)+'...':a).slice(0,4).join(' ');}catch{return '?';}}
function descendants(root){
 if(process.platform!=='linux'||!root)return [];
 try{const fs=require('node:fs'),states=[];for(const name of fs.readdirSync('/proc'))if(/^\d+$/.test(name)){const state=processState(Number(name));if(state)states.push(state);}
  const out=[],queue=[root];while(queue.length&&out.length<20){const parent=queue.shift();for(const state of states)if(state.ppid===parent){out.push(`${state.pid}:${state.state}:${command(state.pid)}`);queue.push(state.pid);}}return out;}
 catch{return [];}
}
function describe(child,started){
 const own=processState(child.pid);
 return `pid ${child.pid} (${child.spawnfile||'?'}${own?`, state ${own.state}`:', gone'}), exit ${child.exitCode??'none'}/${child.signalCode??'none'}, waited ${Date.now()-started} ms, live descendants [${descendants(child.pid).join('; ')||'none'}]`;
}
module.exports={trackChild,waitForClose,waitForGroup,describe};
