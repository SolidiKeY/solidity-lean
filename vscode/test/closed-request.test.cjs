// Regression: closed document accessors must not run before typed stale/cancel refusals.
// Injected request boundary only; native close/reopen observations are separate.
'use strict';
const test=require('node:test'),assert=require('node:assert/strict'),{LanguageClient,LanguageServers}=require('../src/lsp-client.cjs');
function fixture(Type){let reads=0,work=0;const doc={isClosed:true,get version(){reads++;throw Error('closed version accessor');},getText(){reads++;throw Error('closed text accessor');}},client=Object.create(Type.prototype);client.sync=client.settled=client.client=async()=>{work++;throw Error('must not acquire client');};return{doc,client,counts:()=>({reads,work})};}
test('closed direct and managed requests refuse before reading content or acquiring clients',async()=>{for(const Type of [LanguageClient,LanguageServers]){const f=fixture(Type);await assert.rejects(f.client.request('codeAction/resolve',f.doc,{},{}),e=>e.code===-32801);assert.deepEqual(f.counts(),{reads:0,work:0});}});
test('already cancelled requests retain cancellation priority without reading closed content',async()=>{for(const Type of [LanguageClient,LanguageServers]){const f=fixture(Type),c=new AbortController();c.abort();await assert.rejects(f.client.request('codeAction/resolve',f.doc,{},{signal:c.signal}),e=>e.code===-32800);assert.deepEqual(f.counts(),{reads:0,work:0});}});
