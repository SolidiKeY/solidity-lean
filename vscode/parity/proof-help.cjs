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

// This fixture has a single Markdown paragraph and one Solidity code block.
// It is deliberately not a general Markdown renderer or proof-state inference.
function popupExpected(metadata){
 const {binding,expectedHover,status}=metadata;
 assert.equal(status?.uri,binding.uri);assert.equal(status.version,binding.version);assert.equal(status.sourceHash,binding.textHash);assert.equal(status.synchronizationId,binding.synchronizationId);assert.equal(status.state,'running');
 assert.equal(status.functions?.length,1);assert.deepEqual(status.functions[0].range,expectedHover.range);
 const lines=expectedHover.text.split('\n');assert.equal(lines.length,4);assert.equal(lines[1],'```solidity');assert.equal(lines[3],'```');
 return [[{kind:'paragraph',text:lines[0]},{kind:'code',text:lines[2]}],[{kind:'paragraph',text:require('../src/model.cjs').status(status.functions[0])}]];
}
function popupObservation(observed,metadata,hidden=false){
 assert.equal(observed?.activeUri,metadata.binding.uri,'popup active source URI');assert.ok(Number.isFinite(observed.at),'actual renderer observation time');assert.ok(Array.isArray(observed.widgets));
 if(hidden){assert.equal(observed.widgets.length,0,'Escape must remove every visible hover');return;}
 assert.equal(observed.widgets.length,1,'one visible native hover');assert.equal(observed.widgets[0].fullyVisible,true,'hover fully inside viewport');assert.deepEqual(observed.widgets[0].rows,popupExpected(metadata),'exact ordered native Markdown/code/decoration rows');
}
function verificationPopupOrder(records,start,binding,position,hover,report){
 // Preserve the existing one-provider assertion unchanged, then validate the
 // additional UI request independently. Never discard extra requests silently.
 const matching=records.map((r,index)=>({r,index})).filter(({r,index})=>index>=start&&r.direction==='client'&&r.message?.method==='textDocument/hover'&&r.message.params?.textDocument?.uri===binding.uri&&r.message.params.position?.line===position.line&&r.message.params.position?.character===position.character);
 assert.equal(matching.length,2,'exactly API and native popup hover requests');const [api,popup]=matching;assert.notEqual(api.r.message.id,popup.r.message.id);
 for(const query of matching)assert.equal(records.filter(r=>r.direction==='server'&&r.message?.id===query.r.message.id&&(Object.hasOwn(r.message,'result')||Object.hasOwn(r.message,'error'))).length,1,'one response per actual hover request');
 const replies=records.map((r,index)=>({r,index})).filter(({r,index})=>index>popup.index&&r.direction==='server'&&r.message?.id===popup.r.message.id&&(Object.hasOwn(r.message,'result')||Object.hasOwn(r.message,'error')));assert.equal(replies.length,1,'one popup reply');const reply=replies[0];assert.ok(!reply.r.message.error);assert.deepEqual(reply.r.message.result,hover);
 const {wireDocument}=require('./trace-presentation.cjs'),wire=wireDocument(records,popup.index,binding.uri);assert.equal(popup.r.message.params.textDocument.version,binding.version);assert.equal(wire.version,binding.version);assert.equal(wire.textHash,binding.textHash);assert.equal(wire.openIndex,binding.protocolOpenIndex);assert.equal(records[wire.openIndex].message.params.textDocument.synchronizationId,binding.synchronizationId);
 // Replacing the popup pair with inert records retains all original indices,
 // source changes, terminal messages and every other query for the old check.
 const single=records.map((r,index)=>index===popup.index||index===reply.index?{}:r),base=verificationHoverOrder(single,start,binding,position,hover,report);
 assert.ok(base.hoverResponseIndex<popup.index&&popup.index<reply.index&&reply.index<base.terminalIndex,'both real hover replies precede the current terminal');
 return {...base,popupRequestId:popup.r.message.id,popupRequestIndex:popup.index,popupResponseIndex:reply.index,scope:'Two exact real provider replies before actual current verification terminal; rendered popup and dismissal checked separately.'};
}

module.exports={synchronizedBinding,sourceBinding,sameSource,assertCertifiedFailureObservation,currentFailureStatus,menuObservation,proofHoverExpected,verificationHoverOrder,popupExpected,popupObservation,verificationPopupOrder};
