// Closure confirmation is lifecycle evidence, never verifier/proof readiness.
'use strict';
const {terminateTree}=require('./backend.cjs');
const {processState,groupMembers,running}=require('./process-state.cjs');
const closures=new WeakMap(),observations=new WeakMap();
function diagnosticMessage(error){try{return String(error?.message??error);}catch{return 'Unprintable failure';}}
// Enabled explicitly for owned diagnostic fixtures; normal clients allocate no trace.
function enableChildLifetimeObservation(child){if(!observations.has(child))observations.set(child,{events:[],dropped:0});}
function note(child,event,extra={}){try{const o=observations.get(child);if(!o)return;const row={event,wallMs:Date.now(),monotonicMs:require('node:perf_hooks').performance.now(),pid:child.pid,birth:child.processBirth,ownedGroup:child.ownedGroup===true,exitCode:child.exitCode,signalCode:child.signalCode,stdio:child.stdio?.map(s=>s?{destroyed:s.destroyed,closed:s.closed,readableEnded:s.readableEnded,writableEnded:s.writableEnded}:null),...extra};if(o.events.length<256)o.events.push(row);else{o.dropped++;o.last=row;}}catch{}}
function childLifetimeObservation(child){const o=observations.get(child);return o?structuredClone(o):null;}
function measured(child,phase,fn){note(child,phase+'.start');try{const value=fn();note(child,phase+'.end',{...(Array.isArray(value)?{memberCount:value.length,members:value.slice(0,16),membersTruncated:value.length>16}:{})});return value;}catch(error){note(child,phase+'.error',{message:diagnosticMessage(error)});throw error;}}

function trackChild(child){child.processBirth??=processState(child.pid)?.birth;let closed=closures.get(child);if(!closed){note(child,'track.register');closed=new Promise(resolve=>child.once('close',code=>{note(child,'child.close',{code});resolve(code);}));closures.set(child,closed);}return closed;}
async function waitForGroup(child,{deadline=Date.now()+1000,kill=false}={}){
 const started=Date.now();
 note(child,'group.wait',{deadline,kill});if(kill)measured(child,'group.kill',()=>terminateTree(child));
 let members=measured(child,'group.read',()=>groupMembers(child));
 if(members.some(running)){measured(child,'group.kill',()=>terminateTree(child));members=measured(child,'group.read',()=>groupMembers(child));}
 const timely=()=>{if(Date.now()>=deadline){note(child,'group.timeout',{deadline});throw new Error('Owned session retirement was not confirmed before shutdown deadline: '+describe(child,started,members));}};
 timely();
 while(members.some(running)){if(Date.now()>=deadline)throw new Error('Owned session remained live after shutdown deadline: '+describe(child,started,members));await new Promise(setImmediate);members=measured(child,'group.read',()=>groupMembers(child));timely();}
}
// Only the preliminary read can be deferred. Actual close and the fresh final
// group read/retirement below remain required under the same deadline.
function canDeferGroupReadback(child){try{if(!Array.isArray(child.stdio)||child.stdio.length<3||child.channel||child.connected===true)return false;for(let i=0;i<child.stdio.length;i++){const slot=Object.getOwnPropertyDescriptor(child.stdio,String(i));if(!slot||!Object.hasOwn(slot,'value'))return false;const stream=slot.value;if(stream!==null&&(stream===undefined||stream.closed!==true))return false;}return true;}catch{return false;}}
async function waitForClose(child,{closed=trackChild(child),kill=false,timeoutMs=1000,deadline=Date.now()+timeoutMs}={}){
 const started=Date.now();
 note(child,'close.wait',{deadline,kill,timeoutMs});if(kill&&(child.ownedGroup||child.pid&&child.exitCode===null&&child.signalCode===null))measured(child,'close.kill',()=>terminateTree(child));
 // A private-session descendant may retain stdio after its root exits. Retire
 // that owned group before waiting for pipe closure, never treating exit as close.
 let timer,onExit;
 const exitFailure=new Promise((resolve,reject)=>{if(!child.ownedGroup)return;onExit=(...args)=>{note(child,'exit.handler',{delivery:args.length?'event':'already-exited',code:args[0],signal:args[1]});try{if(canDeferGroupReadback(child)){note(child,'exit.group.deferred',{reason:'stdio closed; final readback required'});return;}if(measured(child,'exit.group.read',()=>groupMembers(child)).some(running))measured(child,'exit.group.kill',()=>terminateTree(child));}catch(error){reject(error);}};if(child.exitCode!=null||child.signalCode!=null)onExit();else child.once('exit',onExit);});
 try{await Promise.race([closed,exitFailure,new Promise((resolve,reject)=>{timer=setTimeout(()=>{note(child,'close.timeout',{deadline});reject(new Error('Owned child closure was not confirmed before shutdown deadline: '+describe(child,started)));},Math.max(0,deadline-Date.now()));})]);note(child,'close.promise-fulfilled');await waitForGroup(child,{deadline});note(child,'close.complete');}catch(error){note(child,'close.failure',{message:diagnosticMessage(error)});try{if(observations.has(child))Object.defineProperty(error,'closureObservation',{value:childLifetimeObservation(child),configurable:true});}catch{}throw error;}finally{clearTimeout(timer);if(onExit)child.removeListener('exit',onExit);}
}
// Group failures reuse the final observed process snapshot; no second global scan.
// Shutdown-timeout diagnostics only (no effect on deadlines or decisions): name
// the child and list its live descendants so a CI failure says what held it.
function command(pid){try{return require('node:fs').readFileSync('/proc/'+pid+'/cmdline','utf8').split('\0').filter(Boolean).map(a=>a.length>60?a.slice(0,57)+'...':a).slice(0,4).join(' ');}catch{return '?';}}
function descendants(root,snapshot){
 if(process.platform!=='linux'||!root)return [];
 try{const fs=require('node:fs'),states=snapshot??[];if(!snapshot)for(const name of fs.readdirSync('/proc'))if(/^\d+$/.test(name)){const state=processState(Number(name));if(state)states.push(state);}
  const out=[],queue=[root];while(queue.length&&out.length<20){const parent=queue.shift();for(const state of states)if(state.ppid===parent){out.push(`${state.pid}:${state.state}:${command(state.pid)}`);queue.push(state.pid);}}return out;}
 catch{return [];}
}
function describe(child,started,snapshot){
 try{const own=processState(child.pid);
 return `pid ${child.pid} (${child.spawnfile||'?'}${own?`, state ${own.state}`:', gone'}), exit ${child.exitCode??'none'}/${child.signalCode??'none'}, waited ${Date.now()-started} ms, live descendants [${descendants(child.pid,snapshot).join('; ')||'none'}]`;}
 catch(error){return `pid ${child.pid} (description unavailable: ${error?.message})`;}
}
module.exports={trackChild,waitForClose,waitForGroup,describe,childLifetimeObservation,enableChildLifetimeObservation,canDeferGroupReadback};
