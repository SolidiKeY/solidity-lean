// Injected diagnostic ownership controls; actual compiler/LSP integration is separate.
'use strict';
const test=require('node:test'),assert=require('node:assert/strict'),{SolidityService}=require('../src/lsp-server.cjs');
function fixture(){const service=Object.create(SolidityService.prototype),doc={uri:'file:///owned.sol',path:'/owned.sol',text:'pragma solidity ^0.8.34; contract C {}',version:1,synchronizationId:'open1'},diagnostic={source:'solc',code:1878,severity:2,message:'SPDX license identifier not provided',range:{start:{line:0,character:0},end:{line:0,character:1}}};Object.assign(service,{closed:false,generation:'generation1',docs:new Map([[doc.uri,doc]]),notify(){}});service.diagnostics(doc,[diagnostic]);return{service,doc,diagnostic,query:d=>service.codeActions(doc,{context:{diagnostics:[d]}})};}
test('genuine current compiler warning produces source/version-owned edits',()=>{const f=fixture(),actions=f.query(f.diagnostic);assert.equal(actions.length,3);for(const a of actions){assert.equal(a.edit.documentChanges[0].textDocument.uri,f.doc.uri);assert.equal(a.edit.documentChanges[0].textDocument.version,1);assert.ok(a.edit.documentChanges[0].edits[0].newText.startsWith('// SPDX-License-Identifier:'));}});
test('foreign missing or changed diagnostic cannot authorize a quick fix',()=>{
 for(const mutate of [d=>d.source='foreign',d=>d.range.start.character=1,d=>delete d.range,d=>d.code=5667]){const f=fixture(),d=structuredClone(f.diagnostic);mutate(d);assert.deepEqual(f.query(d),[]);}
 for(const source of ['solidity-lean','other']){const f=fixture();f.service.diagnostics(f.doc,[{...f.diagnostic,source}]);assert.deepEqual(f.query(f.diagnostic),[]);}
});
test('changed source version generation close or reopen invalidates previous diagnostic ownership',()=>{
 for(const mutate of [f=>f.doc.version++,f=>f.doc.uri='file:///foreign.sol',f=>f.doc.text+=' ',f=>f.doc.synchronizationId='open2',f=>f.service.generation='generation2',f=>f.service.docs.delete(f.doc.uri),f=>f.service.docs.set(f.doc.uri,{...f.doc}),f=>f.service.closed=true,f=>f.service.diagnostics(f.doc,[])]){const f=fixture();mutate(f);assert.deepEqual(f.query(f.diagnostic),[]);}
});
test('client message formatting and property order do not replace canonical compiler evidence',()=>{const f=fixture(),d={code:'1878',message:'client shortened message',range:{end:{character:1,line:0},start:{character:0,line:0}}},actions=f.query(d);assert.equal(actions.length,3);assert.equal(actions[0].diagnostics[0].message,f.diagnostic.message);});

test('production editor provider forwards diagnostic source and structured code value (injected API)',async()=>{
 const {fixture}=require('./controller-fixture.cjs'),requests=[];let provider;const e=fixture(undefined,env=>{env.vscode.languages.registerCodeActionsProvider=(_selector,value)=>{provider=value;return{dispose(){}};};env.service.request=async(method,doc,params)=>{requests.push({method,params});return[];};});
 try{const range={start:{line:0,character:0},end:{line:0,character:1}};await provider.provideCodeActions(e.doc,range,{diagnostics:[{range,message:'compiler warning',source:'solc',code:{value:1878},severity:1}]});assert.equal(requests[0].method,'textDocument/codeAction');assert.equal(requests[0].params.context.diagnostics[0].source,'solc');assert.equal(requests[0].params.context.diagnostics[0].code,1878);}finally{await e.api.dispose();}
});

test('published compiler evidence and returned diagnostics are independent snapshots',()=>{const f=fixture(),hint=structuredClone(f.diagnostic);f.diagnostic.message='mutated caller';const first=f.query(hint);assert.notEqual(first[0].diagnostics[0].message,'mutated caller');first[0].diagnostics[0].code=5667;assert.equal(f.query(hint).length,3);});
