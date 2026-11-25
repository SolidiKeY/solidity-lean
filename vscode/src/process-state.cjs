// Linux readback of a known-owned process/session. No process-name/global cleanup authority.
'use strict';
const fs=require('node:fs');
function processState(pid){if(process.platform!=='linux')return null;try{const text=fs.readFileSync('/proc/'+pid+'/stat','utf8'),parts=text.slice(text.lastIndexOf(')')+2).split(' ');return{pid,state:parts[0],ppid:Number(parts[1]),group:Number(parts[2]),session:Number(parts[3]),threads:Number(parts[17]),birth:parts[19],rssPages:Number(parts[21])};}catch(error){if(['ENOENT','ESRCH'].includes(error.code))return null;throw error;}}
function kernelChildIds(parent){
  const tasks=fs.readdirSync('/proc/'+parent.pid+'/task').filter(name=>/^\d+$/.test(name));
  if(!tasks.length)throw Error('No process tasks');
  return [...new Set(tasks.flatMap(tid=>{const text=fs.readFileSync('/proc/'+parent.pid+'/task/'+tid+'/children','utf8').trim();if(!text)return [];const names=text.split(/\s+/);if(!names.every(name=>/^\d+$/.test(name)&&Number.isSafeInteger(Number(name))&&Number(name)>0))throw Error('Invalid child list');return names.map(Number);}))];
}
// Kernel child lists are optional. Always validate PPID and the parent's birth.
function directChildren(parent,observe){
 const note=(event,details)=>{try{observe?.(event,details);}catch{}};
 const current=processState(parent.pid);if(!current)return [];
 if(current.birth!==parent.birth)throw Error('Owned process identity changed; refusing child discovery');
 let ids,mode='kernel-children';note('child.discovery.start',{pid:parent.pid,birth:parent.birth,state:current.state});
 try{
  if(current.state!=='T')throw Error('Parent stop not confirmed');
  ids=kernelChildIds(parent);
 }catch{
  mode='ppid-scan';note('child.discovery.fallback',{pid:parent.pid,birth:parent.birth,reason:current.state!=='T'?'parent-not-stopped':'kernel-child-list-unavailable'});
  ids=fs.readdirSync('/proc').filter(name=>/^\d+$/.test(name)).map(Number);
  // Enumeration is already required here. A fresh confirmed stop can avoid
  // reading every unrelated PID; unavailable lists still use the original IDs.
  if(current.state!=='T'){
   const stopped=processState(parent.pid);if(!stopped){note('child.discovery.stop-check',{pid:parent.pid,birth:parent.birth,state:null});return [];}
   if(stopped.birth!==parent.birth)throw Error('Owned process identity changed; refusing child discovery');
   note('child.discovery.stop-check',{pid:parent.pid,birth:parent.birth,state:stopped.state});
   if(stopped.state==='T'){
    try{
     ids=kernelChildIds(parent);mode='kernel-children-after-stop';
     note('child.discovery.stop-confirmed',{pid:parent.pid,birth:parent.birth,state:stopped.state});
    }catch(error){
     // Diagnostic extraction must not invoke an arbitrary error accessor.
     try{const code=Object.getOwnPropertyDescriptor(error??{},'code')?.value;note('child.discovery.kernel-unavailable-after-stop',{pid:parent.pid,birth:parent.birth,code:typeof code==='string'?code.slice(0,64):'unknown'});}catch{}
    }
   }
  }
 }
 note('child.discovery.enumerated',{pid:parent.pid,birth:parent.birth,mode,candidateCount:ids.length});
 const rows=ids.map(processState).filter(row=>row?.ppid===parent.pid);
 const after=processState(parent.pid);if(!after)return [];
 if(after.birth!==parent.birth)throw Error('Owned process identity changed; refusing child discovery');
 note('child.discovery.end',{pid:parent.pid,birth:parent.birth,mode,childCount:rows.length});return rows;
}
const running=record=>!!record&&!['Z','X'].includes(record.state);
function groupMembers(child){if(process.platform!=='linux'||!child.ownedGroup)return[];const root=processState(child.pid);if(root&&child.processBirth&&root.birth!==child.processBirth)throw new Error('Owned process identity changed; refusing group cleanup');return fs.readdirSync('/proc').filter(name=>/^\d+$/.test(name)).map(Number).map(processState).filter(record=>record?.group===child.pid&&record.session===child.pid);}
function ownedProcess(params,parent){if(!Number.isSafeInteger(params?.pid)||params.pid<=0||params.pid===parent.pid||!/^\d+$/.test(params.birth)||!['analysis','proof','build'].includes(params.kind))throw new Error('Invalid owned process registration');const current=processState(params.pid);if(!running(current)||current.birth!==params.birth||current.ppid!==parent.pid||current.group!==params.pid||current.session!==params.pid)throw new Error('Process is not owned by this server');return{pid:params.pid,processBirth:params.birth,ownedGroup:true,kind:params.kind};}
module.exports={processState,directChildren,running,groupMembers,ownedProcess};
