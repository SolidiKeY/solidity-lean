// Injected callback consistency controls, not native source or row evidence.
'use strict';
const test=require('node:test'),assert=require('node:assert/strict'),fs=require('node:fs'),os=require('node:os'),path=require('node:path');
const {requestPhase,servePhases,paths}=require('../parity/phase-capture.cjs');
const png=Buffer.from('iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAYAAAAfFcSJAAAADUlEQVR4nGNgYGD4DwABBAEAX+XDSwAAAABJRU5ErkJggg==','base64');
const mutations={serializer:r=>{const before=JSON.parse(JSON.stringify(r));r.metadata.binding.uri='file:///foreign.sol';r.toJSON=()=>before;},nestedSerializer:r=>{const before=JSON.parse(JSON.stringify(r.metadata));r.metadata.binding.uri='file:///foreign.sol';r.metadata.toJSON=()=>before;},uri:r=>{r.metadata.binding.uri='file:///foreign.sol';},version:r=>{r.metadata.binding.version++;},source:r=>{r.metadata.source='foreign';},metadata:r=>{r.metadata={};},run:r=>{r.runId='foreign';},phase:r=>{r.phase='menus-tab';},request:r=>{r.requestId='foreign';},requested:r=>{r.requested++;},addition:r=>{r.foreign=true;},deletion:r=>{delete r.metadata;}};
for(const [name,mutate] of Object.entries(mutations))test('phase refuses callback request mutation: '+name,async()=>{
 const dir=fs.mkdtempSync(path.join(os.tmpdir(),'phase-request-'));try{
  const pending=requestPhase(dir,'run','menus-source',{binding:{uri:'file:///owned.sol',version:1},source:'owned'},1000),rejected=assert.rejects(pending,/request changed during capture/),p=paths(dir,'menus-source'),original=fs.readFileSync(p.request,'utf8');
  await servePhases(dir,'run',async(d,request)=>{mutate(request);fs.writeFileSync(path.join(d,'screenshot.png'),png);return{captured:true,screenshot:true};},new Set());await rejected;
  const reply=JSON.parse(fs.readFileSync(p.reply));assert.equal(reply.status,'failed');assert.equal(reply.imageSha256,undefined);assert.equal(reply.runId,'run');assert.equal(reply.phase,'menus-source');assert.equal(fs.readFileSync(p.request,'utf8'),original);assert.deepEqual(fs.readFileSync(path.join(p.dir,'screenshot.png')),png);
 }finally{fs.rmSync(dir,{recursive:true,force:true});}
});
test('read-only callback preserves the original request and succeeds',async()=>{
 const dir=fs.mkdtempSync(path.join(os.tmpdir(),'phase-request-'));try{
  const pending=requestPhase(dir,'run','menus-source',{binding:{uri:'file:///owned.sol',version:1}},1000),p=paths(dir,'menus-source'),original=fs.readFileSync(p.request,'utf8');
  await servePhases(dir,'run',async(d,r)=>{assert.equal(r.metadata.binding.uri,'file:///owned.sol');fs.writeFileSync(path.join(d,'screenshot.png'),png);return{captured:true,screenshot:true};},new Set());assert.equal((await pending).status,'captured');assert.equal(fs.readFileSync(p.request,'utf8'),original);
 }finally{fs.rmSync(dir,{recursive:true,force:true});}
});
