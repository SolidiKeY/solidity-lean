// Test-fixture cleanup observations never establish proof or rendered/runtime parity.
'use strict';
const fs=require('node:fs'),{performance}=require('node:perf_hooks'),{processState,groupMembers}=require('../src/process-state.cjs'),{childLifetimeObservation}=require('../src/child-lifetime.cjs');
function errorText(error){if(error===null||!['object','function'].includes(typeof error))return String(error);try{const value=Object.getOwnPropertyDescriptor(error,'message')?.value;return typeof value==='string'?value:'Unprintable failure';}catch{return 'Unprintable failure';}}
function snapshot(client){const c=client.child;if(!c)return{child:null};return{pid:c.pid,birth:c.processBirth,process:processState(c.pid),group:groupMembers(c),exitCode:c.exitCode,signalCode:c.signalCode,confirmedClose:client.childClosureConfirmed===true,lifetime:childLifetimeObservation(c),stdio:c.stdio?.map(s=>s?{destroyed:s.destroyed,closed:s.closed,readableEnded:s.readableEnded,writableEnded:s.writableEnded}:null)};}
async function settleFixtures(resources,{record=()=>{},remove=directory=>fs.rmSync(directory,{recursive:true,force:true})}={}){
 const readbackErrors=[],read=client=>{try{return snapshot(client);}catch(error){readbackErrors.push(error);return{readbackError:errorText(error)};}};
 const rows=resources.map(({name,f,client,events})=>({name,directory:f.directory,events,before:read(client),started:performance.now()}));
 const outcomes=await Promise.allSettled(resources.map(async({client},index)=>{try{await client.dispose();}finally{rows[index].disposalSettled=performance.now();}}));
 // Diagnostic scans and file removal must not consume sibling disposal deadlines.
 const postErrors=[];
 for(const [index,{f,client}]of resources.entries()){
  const row=rows[index];row.afterBarrier='all-disposals-settled';row.afterReadStarted=performance.now();
  try{row.after=read(client);if(outcomes[index].status==='fulfilled'&&!Object.hasOwn(row.before,'readbackError')&&!Object.hasOwn(row.after,'readbackError'))remove(f.directory);}
  catch(error){if(outcomes[index].status==='fulfilled')outcomes[index]={status:'rejected',reason:error};else postErrors.push(error);}
  finally{row.settled=performance.now();}
 }
 const errors=[...readbackErrors,...postErrors];for(const [i,outcome]of outcomes.entries()){rows[i].status=outcome.status;if(outcome.status==='rejected'){rows[i].error=errorText(outcome.reason);errors.push(outcome.reason);}}
 try{record(rows);}catch(error){errors.push(error);}
 if(errors.length)throw Object.assign(new AggregateError(errors,'Fixture cleanup failed; every admitted fixture was attempted'),{cleanup:rows});
 return rows;
}
module.exports={settleFixtures};
