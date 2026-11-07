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

// Source-derived expectation for the existing one-function shared proof-help fixture.
function proofHoverExpected(text){
 const {position}=require('../src/language-services.cjs'),start=text.indexOf('function f0()'),name=text.indexOf('f0()',start),brace=text.indexOf('{',start);assert.ok(start>=0&&name>=start&&brace>name,'shared f0 declaration');
 const comment=text.slice(0,start).trimEnd().split('\n').at(-1).trim();assert.ok(comment.startsWith('/// '),'actual fixture documentation');
 return {position:position(text,name),text:comment.slice(4)+'\n```solidity\n'+text.slice(start,brace).trim()+'\n```',range:{start:position(text,name),end:position(text,name+2)}};
}
function verificationHoverOrder(records,start,binding,position,observedHover,observedReport){
 const {wireDocument}=require('./trace-presentation.cjs'),requests=method=>records.map((r,index)=>({r,index})).filter(({r,index})=>index>=start&&r.direction==='client'&&r.message?.method===method&&r.message.params?.textDocument?.uri===binding.uri),proofs=requests('solidityLean/verify'),hovers=requests('textDocument/hover').filter(({r})=>r.message.params.position?.line===position.line&&r.message.params.position?.character===position.character);
 assert.equal(proofs.length,1,'one genuine verification request');assert.equal(hovers.length,1,'one unambiguous native provider hover');const proof=proofs[0],hover=hovers[0];assert.equal(proof.r.message.params.options?.certify,true);assert.equal(proof.r.message.params.options?.counterexamples,true);
 for(const query of [proof,hover]){assert.equal(query.r.message.params.textDocument.version,binding.version);const wire=wireDocument(records,query.index,binding.uri);assert.equal(wire.version,binding.version);assert.equal(wire.textHash,binding.textHash);assert.equal(wire.openIndex,binding.protocolOpenIndex);assert.equal(records[wire.openIndex].message.params.textDocument.synchronizationId,binding.synchronizationId);}
 const response=query=>{const index=records.findIndex((r,i)=>i>query.index&&r.direction==='server'&&r.message?.id===query.r.message.id&&(Object.hasOwn(r.message,'result')||Object.hasOwn(r.message,'error')));assert.ok(index>query.index,'actual matching response');assert.ok(!records[index].message.error,'successful response, not cancellation/error');return index;},proofResponse=response(proof),hoverResponse=response(hover);
 assert.ok(proof.index<hover.index&&hover.index<hoverResponse&&hoverResponse<proofResponse,'hover response precedes verification completion');
 assert.deepEqual(records[hoverResponse].message.result,observedHover,'native provider equals actual wire result');assert.deepEqual(records[proofResponse].message.result,observedReport,'observed certified report equals actual wire result');
 const terminals=records.map((r,index)=>({r,index})).filter(({r,index})=>index>proof.index&&index<=proofResponse&&r.direction==='server'&&r.message?.method==='solidityLean/status'&&r.message.params?.uri===binding.uri&&r.message.params.version===binding.version&&r.message.params.sourceHash===binding.textHash&&r.message.params.synchronizationId===binding.synchronizationId&&r.message.params.state==='complete');assert.equal(terminals.length,1,'one current terminal status');assert.ok(hoverResponse<terminals[0].index,'hover precedes actual terminal notification');
 assert.equal(records.slice(proof.index,proofResponse+1).filter(r=>r.direction==='client'&&['textDocument/didOpen','textDocument/didChange','textDocument/didClose'].includes(r.message?.method)&&r.message.params?.textDocument?.uri===binding.uri).length,0,'stable source/open interval');
 return {binding,proofRequestId:proof.r.message.id,hoverRequestId:hover.r.message.id,proofRequestIndex:proof.index,hoverRequestIndex:hover.index,hoverResponseIndex:hoverResponse,terminalIndex:terminals[0].index,proofResponseIndex:proofResponse,scope:'Observed provider response before native verification-request terminal/response; no inferred internal proof stage or rendered hover popup.'};
}

module.exports={synchronizedBinding,sourceBinding,sameSource,assertCertifiedFailureObservation,currentFailureStatus,menuObservation,proofHoverExpected,verificationHoverOrder};
