// Public event/getter correlation only, never proof or trigger-causality evidence.
'use strict';
const assert=require('node:assert/strict'),{performance}=require('node:perf_hooks'),{randomUUID}=require('node:crypto');
const base=()=>require('./related-diagnostics.cjs');
function witness(changes,b,diagnostics,publicationIndex,protocol,start,end){
 assert.ok(Array.isArray(changes.errors)&&changes.errors.length===0,'Diagnostic event observer failed');
 for(let i=changes.rows.length-1;i>=0;i--){const row=changes.rows[i];if(row.status!=='observed'||row.atMonotonicMs<start||row.atMonotonicMs>=end||row.wireEnd>protocol.length)continue;
  const value=row.resources.find(r=>r.uri===b.uri);if(!value?.binding||JSON.stringify(value.binding)!==JSON.stringify(b)||JSON.stringify(value.after)!==JSON.stringify(b)||JSON.stringify(value.diagnostics)!==JSON.stringify(diagnostics))continue;
  const selection=base().currentPublication(protocol.slice(0,row.wireEnd),b);if(selection.status==='current'&&selection.found.index===publicationIndex)return i;
 }return null;
}
function observe({vscode,sessionFor,wire,subscribe,now=()=>performance.now()}){
 const changes={profile:'public-v1',registrationSource:subscribe?'shared-public-observer':'direct-public-api',observerId:randomUUID(),rows:[],errors:[],disposed:false};let registration;
 const callback=event=>{const row={observerId:changes.observerId,sequence:changes.rows.length+1,atMonotonicMs:now(),status:'started',resources:[]};changes.rows.push(row);
  try{assert.equal(changes.disposed,false,'Callback after owned listener disposal');assert.ok(Array.isArray(event.uris));row.changedUris=event.uris.map(uri=>uri.toString());assert.equal(new Set(row.changedUris).size,row.changedUris.length);row.wireEnd=wire().length;
   for(const uri of event.uris){const docs=vscode.workspace.textDocuments.filter(doc=>doc.uri.toString()===uri.toString()),value={uri:uri.toString()};row.resources.push(value);if(docs.length!==1||docs[0].isClosed||vscode.window.activeTextEditor?.document!==docs[0]){value.unavailable={documents:docs.length,reason:'not-unique-current-active-document'};continue;}const doc=docs[0];value.binding=base().documentBinding(vscode,doc,sessionFor);value.diagnostics=base().diagnosticSnapshot(vscode.languages.getDiagnostics(uri));value.after=base().documentBinding(vscode,doc,sessionFor);assert.deepEqual(value.after,value.binding,'Document changed during public event callback');}
   row.status='observed';
  }catch(error){row.status='failed';row.error=error.stack;changes.errors.push(error.stack);}
 };
 registration=subscribe?subscribe(callback):vscode.languages.onDidChangeDiagnostics(callback);
 return{changes,witness:(b,d,index,protocol,start,end)=>witness(changes,b,d,index,protocol,start,end),dispose(){if(changes.disposed)return;changes.disposed=true;const owned=registration;registration=null;try{owned.dispose();}catch(error){changes.errors.push(error.stack);throw error;}}};
}
function validate(changes,steps,protocol){
 assert.equal(changes?.profile,'public-v1');assert.ok(['shared-public-observer','direct-public-api'].includes(changes.registrationSource));assert.match(changes.observerId,/^[a-f0-9-]{36}$/);assert.equal(changes.disposed,true);assert.ok(Array.isArray(changes.errors)&&changes.errors.length===0);assert.ok(Array.isArray(changes.rows)&&changes.rows.length);
 let previous=-1,previousWireEnd=0;for(const [i,row]of changes.rows.entries()){assert.equal(row.observerId,changes.observerId);assert.equal(row.sequence,i+1);assert.equal(row.status,'observed');assert.ok(!row.error);assert.ok(Number.isFinite(row.atMonotonicMs)&&row.atMonotonicMs>=0&&row.atMonotonicMs>=previous);previous=row.atMonotonicMs;assert.ok(Number.isSafeInteger(row.wireEnd)&&row.wireEnd>=previousWireEnd&&row.wireEnd<=protocol.length);previousWireEnd=row.wireEnd;assert.ok(Array.isArray(row.changedUris)&&row.changedUris.every(u=>typeof u==='string'));assert.equal(new Set(row.changedUris).size,row.changedUris.length);assert.deepEqual(row.resources.map(r=>r.uri),row.changedUris);}
 for(const s of steps){assert.ok(Number.isFinite(s.startedMonotonicMs)&&s.startedMonotonicMs>=0);assert.ok(Number.isSafeInteger(s.diagnosticEventIndex)&&s.diagnosticEventIndex>=0&&s.diagnosticEventIndex<changes.rows.length);assert.equal(witness(changes,s.before,s.diagnostics,s.publicationIndex,protocol.slice(0,s.wireEnd),s.startedMonotonicMs,s.startedMonotonicMs+s.elapsedMs),s.diagnosticEventIndex,'No current public diagnostic event/getter correlation');}
}
module.exports={observe,witness,validate};
