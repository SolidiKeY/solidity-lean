// Injected acknowledgement serialization controls; no native/rendered/row evidence.
'use strict';
const test=require('node:test'),assert=require('node:assert/strict'),fs=require('node:fs'),os=require('node:os'),path=require('node:path');
const {requestPhase,servePhases,paths}=require('../parity/phase-capture.cjs');
const png=Buffer.from('iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAYAAAAfFcSJAAAADUlEQVR4nGNgYGD4DwABBAEAX+XDSwAAAABJRU5ErkJggg==','base64');
const cases={mutatingError:()=>({captured:true,screenshot:true,toJSON(){this.error=false;return{captured:true,screenshot:true};}}),mutatingRefusal:()=>({captured:true,screenshot:true,toJSON(){this.captured=false;return{captured:true,screenshot:true};}}),circular:()=>{const r={captured:true,screenshot:true};r.self=r;return r;},bigint:()=>({captured:true,screenshot:true,value:1n}),throwingSerializer:()=>({captured:true,screenshot:true,toJSON(){throw Error('cannot serialize capture');}}),serializedRefusal:()=>({captured:true,screenshot:true,toJSON(){return{captured:false,screenshot:true};}}),serializedError:()=>({captured:true,screenshot:true,toJSON(){return{captured:true,screenshot:true,error:false};}}),hiddenError:()=>({captured:true,screenshot:true,error:false,toJSON(){return{captured:true,screenshot:true};}}),hiddenRefusal:()=>({captured:false,screenshot:true,toJSON(){return{captured:true,screenshot:true};}})};
for(const [name,create] of Object.entries(cases))test('phase retains serializable refusal for capture result '+name,async()=>{
 const dir=fs.mkdtempSync(path.join(os.tmpdir(),'phase-json-'));try{
  const pending=requestPhase(dir,'run','menus-source',{},1000),rejected=assert.rejects(pending,/failed/),p=paths(dir,'menus-source');
  await servePhases(dir,'run',async d=>{fs.writeFileSync(path.join(d,'screenshot.png'),png);return create();},new Set());await rejected;
  const reply=JSON.parse(fs.readFileSync(p.reply));assert.equal(reply.status,'failed');assert.equal(typeof reply.error,'string');assert.ok(reply.error.length);assert.equal(reply.imageSha256,undefined);assert.deepEqual(fs.readFileSync(path.join(p.dir,'screenshot.png')),png);
 }finally{fs.rmSync(dir,{recursive:true,force:true});}
});
test('healthy JSON capture details survive detached acknowledgement',async()=>{
 const dir=fs.mkdtempSync(path.join(os.tmpdir(),'phase-json-'));try{
  const capture={captured:true,screenshot:true,details:{owned:['source',1]}},pending=requestPhase(dir,'run','menus-source',{},1000);
  await servePhases(dir,'run',async d=>{fs.writeFileSync(path.join(d,'screenshot.png'),png);return capture;},new Set());assert.deepEqual((await pending).capture,capture);
 }finally{fs.rmSync(dir,{recursive:true,force:true});}
});
