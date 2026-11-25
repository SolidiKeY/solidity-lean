'use strict';
const {test}=require('node:test');
const assert=require('node:assert/strict');
const fs=require('node:fs');
const {tmpdir}=require('node:os');
const {join}=require('node:path');
const {pathToFileURL}=require('node:url');
const {SolidityService}=require('../src/lsp-server.cjs');
function setup(t,code='1686'){
  const root=fs.mkdtempSync(join(tmpdir(),'failed-code-actions-')),events=[],state={calls:0,generation:'one'};
  const service=new SolidityService({notify:(method,params)=>events.push({method,params})},root,{automaticVerification:'never'},{fingerprint:()=>state.generation});
  const path=join(root,'C.sol'),text='import "./D.sol"; contract C {}',dependency=join(root,'D.sol');
  fs.writeFileSync(dependency,'contract D {}');fs.writeFileSync(path,text);
  service.analysisPool.run=async()=>{state.calls++;throw Object.assign(new Error('compiler failure'),{diagnostics:[{severity:'error',errorCode:code,message:'compiler failure',sourceLocation:{file:path,start:0,end:1}}]});};
  const uri=pathToFileURL(path).href,doc=service.open({uri,text,version:1,synchronizationId:'first'});clearTimeout(doc.timer);
  t.after(()=>{service.dispose();fs.rmSync(root,{recursive:true,force:true});});
  const request=()=>({textDocument:{uri,version:doc.version},context:{diagnostics:structuredClone(doc.publishedDiagnostics.values)}});
  return {root,service,doc,state,events,dependency,request};
}
test('unsupported fixes reuse only the actual current failed batch without recompilation or publication',async t=>{
  const s=setup(t);await assert.rejects(s.service.analyze(s.doc),/compiler failure/);
  const count=s.events.length,batch=s.doc.publishedDiagnostics;
  for(let i=0;i<3;i++)assert.deepEqual(await s.service.language('textDocument/codeAction',s.request()),[]);
  assert.equal(s.state.calls,1);assert.equal(s.events.length,count);assert.equal(s.doc.publishedDiagnostics,batch);assert.equal(s.doc.codeActionSet,null);
});
test('supported SPDX fixes retain normal analysis and exact offered edits',async t=>{
  const s=setup(t,'1878');await assert.rejects(s.service.analyze(s.doc));
  const actions=await s.service.language('textDocument/codeAction',s.request());
  assert.equal(s.state.calls,2);assert.equal(actions.length,3);assert.equal(actions[1].edit.documentChanges[0].edits[0].newText,'// SPDX-License-Identifier: MIT\n');
});
for(const mutation of ['dependency','settings','backend','publication','session','source','dependency-reopen'])test('failed batch is not reused after '+mutation,async t=>{
  const s=setup(t);
  if(mutation==='dependency-reopen'){
    const doc=s.service.open({uri:pathToFileURL(s.dependency).href,text:fs.readFileSync(s.dependency,'utf8'),version:1,synchronizationId:'dep1'});clearTimeout(doc.timer);
  }
  await assert.rejects(s.service.analyze(s.doc));const params=s.request();
  if(mutation==='dependency')fs.writeFileSync(s.dependency,'contract Changed {}');
  if(mutation==='settings')s.service.settings.timeoutMs++;
  if(mutation==='backend'){const run=s.service.analysisPool.run;s.state.generation='two';s.service.refresh();s.service.analysisPool.run=run;}
  if(mutation==='publication')s.service.diagnostics(s.doc,s.doc.publishedDiagnostics.values);
  if(mutation==='session')s.doc.synchronizationId='second';
  if(mutation==='source')s.doc.text+=' ';
  if(mutation==='dependency-reopen'){
    const uri=pathToFileURL(s.dependency).href,old=s.service.docs.get(uri);s.service.docs.set(uri,{...old,synchronizationId:'dep2'});
  }
  await s.service.language('textDocument/codeAction',params);assert.equal(s.state.calls,2);
});
test('foreign or missing facts cannot skip analysis, and cancelled queries do no work',async t=>{
  const s=setup(t);await assert.rejects(s.service.analyze(s.doc));
  const params=s.request();params.context.diagnostics[0].source='foreign';
  await s.service.language('textDocument/codeAction',params);assert.equal(s.state.calls,2);
  const controller=new AbortController();controller.abort();
  await assert.rejects(s.service.language('textDocument/codeAction',s.request(),controller.signal),e=>e.code===-32800);assert.equal(s.state.calls,2);
});

test('primary close/reopen and a newly opened dependency require fresh analysis',async t=>{
  const s=setup(t);await assert.rejects(s.service.analyze(s.doc));
  const old=s.doc,params=s.request();s.service.close(old.uri);
  const reopened=s.service.open({uri:old.uri,text:old.text,version:old.version,synchronizationId:old.synchronizationId});clearTimeout(reopened.timer);
  await s.service.language('textDocument/codeAction',params);assert.equal(s.state.calls,2);assert.notEqual(reopened,old);
  const dep=s.service.open({uri:pathToFileURL(s.dependency).href,text:fs.readFileSync(s.dependency,'utf8'),version:1});clearTimeout(dep.timer);
  await s.service.language('textDocument/codeAction',params);assert.equal(s.state.calls,3);
});
test('empty and malformed kind filters preserve refusal and do not reuse a failed batch',async t=>{
  const s=setup(t);await assert.rejects(s.service.analyze(s.doc));
  const empty=s.request();empty.context.only=[];
  assert.deepEqual(await s.service.language('textDocument/codeAction',empty),[]);assert.equal(s.state.calls,2);
  const bad=s.request();bad.context.only=[7];
  await assert.rejects(s.service.language('textDocument/codeAction',bad),e=>e.code===-32602);
});

test('an explicitly empty diagnostic request returns no fixes without republishing a current failure',async t=>{
  const s=setup(t);await assert.rejects(s.service.analyze(s.doc));const batch=s.doc.publishedDiagnostics,count=s.events.length;
  const params=s.request();params.context.diagnostics=[];
  assert.deepEqual(await s.service.language('textDocument/codeAction',params),[]);
  assert.equal(s.state.calls,1);assert.equal(s.doc.publishedDiagnostics,batch);assert.equal(s.events.length,count);
  delete params.context.diagnostics;await s.service.language('textDocument/codeAction',params);assert.equal(s.state.calls,2);
});
