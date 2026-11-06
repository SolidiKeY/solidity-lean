// Assertions on actual runtime observations; injected unit data is never a certificate.
'use strict';
const assert=require('node:assert/strict'),{createHash}=require('node:crypto'),{validRange}=require('../src/model.cjs');
const digest=text=>createHash('sha256').update(text).digest('hex');
async function synchronizedBinding(service,doc,bind){
 const version=doc.version,text=doc.getText();await service.open(doc);assert.ok(!doc.isClosed&&doc.version===version&&doc.getText()===text,'source changed during protocol synchronization');return bind();
}
function sourceBinding(doc,session,wire){
 assert.ok(Number.isSafeInteger(doc.version)&&doc.version>0,'current integer version');assert.ok(!doc.isClosed&&typeof session==='string'&&session.length,'live document session');const textHash=digest(doc.getText());assert.equal(wire.version,doc.version);assert.equal(wire.textHash,textHash);assert.ok(Number.isSafeInteger(wire.openIndex)&&wire.openIndex>=0);assert.ok(typeof wire.synchronizationId==='string'&&wire.synchronizationId.length,'real synchronization identity');
 return {uri:doc.uri.toString(),version:doc.version,textHash,session,synchronizationId:wire.synchronizationId,protocolOpenIndex:wire.openIndex};
}
function sameSource(before,after){assert.deepEqual(after,before,'source/session/version/text/open ownership changed');}
function assertCertifiedFailureObservation(report,binding,source){
 assert.deepEqual(report.errors,[]);assert.equal(report.results?.length,1);const row=report.results[0];
 assert.equal(row.function,'f0');assert.equal(row.signature,'f0()');assert.equal(row.source,source);assert.equal(row.sourceHash,binding.textHash);assert.equal(row.status,'refuted');assert.notEqual(row.verification,'direct');assert.ok(Number.isSafeInteger(row.sourceId)&&row.sourceId>=0&&validRange(row.range));
 assert.equal(row.counterexample?.certified,true);assert.equal(row.counterexample.goalKind,'fmlValid');assert.match(row.counterexample.certificateDeclaration,/\.refuted$/);assert.ok(Array.isArray(row.counterexample.axioms)&&row.counterexample.axioms.every(x=>['propext','Classical.choice','Quot.sound'].includes(x)));assert.equal(report.backend?.kind,'lean');assert.ok(Number.isSafeInteger(report.backend?.leanServerPid)&&report.backend.leanServerPid>0,'actual Lean backend identity');
 return row;
}
function currentFailureStatus(state,binding,row){
 const functionRow=state?.functions?.[0],range=functionRow?.range;
 return state?.uri===binding.uri&&state.version===binding.version&&state.sourceHash===binding.textHash&&state.synchronizationId===binding.synchronizationId&&state.state==='complete'&&state.progressScope==='functions'&&state.functions.length===1&&functionRow.status==='refuted'&&functionRow.name===row.contract+'.'+row.signature&&validRange(range)&&['start','end'].every(edge=>['line','character'].every(key=>range[edge][key]===row.range[edge][key]));
}
function menuObservation(observed,binding,label){
 assert.equal(observed.activeUri,binding.uri);assert.equal(observed.inputFocused,true);for(const expected of ['Help with a proof','Proof documentation index'])assert.equal(observed.items.filter(item=>item.label===expected).length,1,'one actual native action '+expected);assert.ok(observed.items.some(item=>item.label===label));
}
module.exports={synchronizedBinding,sourceBinding,sameSource,assertCertifiedFailureObservation,currentFailureStatus,menuObservation};
