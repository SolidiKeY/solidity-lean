// Test-fixture cleanup observations never establish proof or rendered/runtime parity.
'use strict';
const fs=require('node:fs'),{performance}=require('node:perf_hooks'),{processState,groupMembers}=require('../src/process-state.cjs');
function snapshot(client){const c=client.child;if(!c)return{child:null};return{pid:c.pid,birth:c.processBirth,process:processState(c.pid),group:groupMembers(c),exitCode:c.exitCode,signalCode:c.signalCode,confirmedClose:client.childClosureConfirmed===true,stdio:c.stdio?.map(s=>s?{destroyed:s.destroyed,closed:s.closed,readableEnded:s.readableEnded,writableEnded:s.writableEnded}:null)};}
async function settleFixtures(resources,{record=()=>{},remove=directory=>fs.rmSync(directory,{recursive:true,force:true})}={}){
 const readbackErrors=[],read=client=>{try{return snapshot(client);}catch(error){readbackErrors.push(error);return{readbackError:error.message};}};
 const rows=resources.map(({name,f,client,events})=>({name,directory:f.directory,events,before:read(client),started:performance.now()}));
 const outcomes=await Promise.allSettled(resources.map(async({f,client},index)=>{try{await client.dispose();rows[index].after=read(client);if(!rows[index].before.readbackError&&!rows[index].after.readbackError)remove(f.directory);}finally{rows[index].settled=performance.now();rows[index].after??=read(client);}}));
 const errors=[...readbackErrors];for(const [i,outcome]of outcomes.entries()){rows[i].status=outcome.status;if(outcome.status==='rejected'){rows[i].error=outcome.reason?.message;errors.push(outcome.reason);}}
 try{record(rows);}catch(error){errors.push(error);}
 if(errors.length)throw Object.assign(new AggregateError(errors,'Fixture cleanup failed; every admitted fixture was attempted'),{cleanup:rows});
 return rows;
}
module.exports={settleFixtures};
