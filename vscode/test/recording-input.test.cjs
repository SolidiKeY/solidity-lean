// Injected filesystem adversaries, not native editor/solver observations.
'use strict';
const test=require('node:test'),assert=require('node:assert/strict'),fs=require('node:fs'),path=require('node:path'),os=require('node:os'),{recordings}=require('./recordings.cjs');
test('optional native recordings skip only wholly absent inputs; partial/linked inputs fail',()=>{
 const root=fs.mkdtempSync(path.join(os.tmpdir(),'parity-recording-inputs-')),a=path.join(root,'input/a.json'),b=path.join(root,'input/b.json');
 try{
  assert.equal(recordings([a,b],root),null);fs.mkdirSync(path.dirname(a));fs.writeFileSync(a,'recorded A');assert.throws(()=>recordings([a,b],root),/Incomplete native recording/);fs.writeFileSync(b,'recorded B');assert.deepEqual(recordings([a,b],root),['recorded A','recorded B']);
  fs.unlinkSync(b);fs.symlinkSync(path.join(root,'absent'),b);assert.throws(()=>recordings([a,b],root),/Unsafe symbolic/);fs.unlinkSync(b);fs.unlinkSync(a);fs.rmdirSync(path.dirname(a));fs.symlinkSync(path.join(root,'absent-directory'),path.dirname(a),'dir');assert.throws(()=>recordings([a,b],root),/Unsafe symbolic/);
 }finally{fs.rmSync(root,{recursive:true,force:true});}
});
