'use strict';
const {test}=require('node:test'),assert=require('node:assert/strict'),fs=require('node:fs'),path=require('node:path'),os=require('node:os'),{createHash}=require('node:crypto');
const {checkDirect,directFingerprint}=require('../src/direct-runtime.cjs');
const sha=b=>createHash('sha256').update(b).digest('hex');
function fixture(){
 const root=fs.mkdtempSync(path.join(os.tmpdir(),'direct-metadata-')),dir=path.join(root,'.lake/direct-runtime');fs.mkdirSync(dir,{recursive:true});fs.mkdirSync(path.join(root,'Solidity/Tools'),{recursive:true});
 const source=path.join(root,'Solidity/Tools/DirectRuntime.lean');fs.writeFileSync(source,'-- explicit test-only model');fs.writeFileSync(path.join(root,'lean-toolchain'),'leanprover/lean4:v4.24.0');
 const js="module.exports=async()=>({ccall:(name,_type,_args,args)=>name==='direct_init'?0:JSON.stringify({results:[{sourceId:1,function:'f',status:'proved',verification:'direct'}]})});";
 fs.writeFileSync(path.join(dir,'direct.js'),js);fs.writeFileSync(path.join(dir,'direct.wasm'),'test-only fake image');
 const manifest={version:1,toolchain:'leanprover/lean4:v4.24.0',leanCommit:'797c613eb9b6d4ec95db23e3e00af9ac6657f24b',sourceFiles:[{module:'Solidity.Tools.DirectRuntime',sourceSha256:sha(fs.readFileSync(source))}],javascript:sha(js),wasm:sha(fs.readFileSync(path.join(dir,'direct.wasm')))};
 fs.writeFileSync(path.join(dir,'build.json'),JSON.stringify(manifest));
 const contract={nodes:[{id:1,name:'f',nodeType:'FunctionDefinition',parameters:{parameters:[{typeDescriptions:{typeString:'uint256'}}]}}]};return {root,dir,source,contract};
}
test('direct selection preserves certified requests and matches full signatures',async()=>{
 const f=fixture();try{
  assert.equal(await checkDirect(f.root,f.contract,{certify:true}),null);assert.equal(await checkDirect(f.root,f.contract,{function:'f(uint8)'}),null);
  const r=await checkDirect(f.root,f.contract,{function:'f(uint)'});assert.equal(r.results[0].signature,'f(uint)');assert.equal(r.timings.environmentImports,0);
 }finally{fs.rmSync(f.root,{recursive:true,force:true});}
});
test('model edits invalidate the fingerprint and reject the stale executable',async()=>{
 const f=fixture();try{
  assert.ok(await checkDirect(f.root,f.contract,{}));const before=directFingerprint(f.root);fs.appendFileSync(f.source,'\n-- changed');
  assert.notEqual(directFingerprint(f.root),before);assert.equal(await checkDirect(f.root,f.contract,{}),null);
 }finally{fs.rmSync(f.root,{recursive:true,force:true});}
});
test('changed executable bytes are rejected without disturbing general checking',async()=>{
 const f=fixture();try{assert.ok(await checkDirect(f.root,f.contract,{}));fs.appendFileSync(path.join(f.dir,'direct.wasm'),'corrupt');assert.equal(await checkDirect(f.root,f.contract,{}),null);}
 finally{fs.rmSync(f.root,{recursive:true,force:true});}
});
