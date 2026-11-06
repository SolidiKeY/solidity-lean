'use strict';
const {test}=require('node:test'),assert=require('node:assert/strict'),fs=require('node:fs'),path=require('node:path'),os=require('node:os'),{createHash}=require('node:crypto');
const {checkDirect,directFingerprint}=require('../src/direct-runtime.cjs');
const {requestFor,unknownResult}=require('../src/direct-model.cjs');
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

test('a full signature selects one compiler declaration even for overloads',()=>{
 const f=fixture();try{
  const first={...f.contract.nodes[0],visibility:'public',kind:'function'};
  const second={...first,id:2,parameters:{parameters:[{typeDescriptions:{typeString:'bool'}}]}};
  const contract={nodes:[first,second]};
  assert.equal(requestFor(contract,{function:'f(uint)'}).sourceId,1);
  assert.deepEqual(unknownResult(contract,{function:'f(bool)'},'unsupported').results.map(r=>r.sourceId),[2]);
  const invalid=unknownResult(contract,{function:'missing'},'unsupported');
  assert.deepEqual(invalid.results,[]);assert.equal(invalid.errors[0].stage,'selection');
 }finally{fs.rmSync(f.root,{recursive:true,force:true});}
});

test('unsupported inheritance still reports inherited public declarations',()=>{
 const declaration={id:3,name:'f',kind:'function',nodeType:'FunctionDefinition',visibility:'public',parameters:{parameters:[]}};
 const base={id:1,nodes:[declaration]},derived={id:2,nodes:[],linearizedBaseContracts:[2,1]};
 assert.deepEqual(unknownResult(derived,{},'inheritance',[base,derived]).results.map(r=>[r.sourceId,r.status]),[[3,'unsupported']]);
});

test('changing the compiled ABI bridge invalidates an executable',async()=>{
 const f=fixture();try{
  fs.mkdirSync(path.join(f.root,'web/browser'),{recursive:true});
  const bridge=path.join(f.root,'web/browser/direct-bridge.c');fs.writeFileSync(bridge,'bridge snapshot');
  const manifest=JSON.parse(fs.readFileSync(path.join(f.dir,'build.json'),'utf8'));manifest.bridgeSha256=sha(fs.readFileSync(bridge));
  fs.writeFileSync(path.join(f.dir,'build.json'),JSON.stringify(manifest));
  assert.ok(await checkDirect(f.root,f.contract,{}));const before=directFingerprint(f.root);
  fs.appendFileSync(bridge,' changed');assert.notEqual(directFingerprint(f.root),before);
  assert.equal(await checkDirect(f.root,f.contract,{}),null);
 }finally{fs.rmSync(f.root,{recursive:true,force:true});}
});

test('missing runtime keeps constructor-only obligations visible',()=>{
 const constructor={id:3,name:'',kind:'constructor',nodeType:'FunctionDefinition',visibility:'public',parameters:{parameters:[]}};
 const result=unknownResult({id:1,nodes:[constructor]}, {},'missing runtime');
 assert.deepEqual(result.results.map(r=>[r.sourceId,r.function,r.status]),[[3,'constructor','unsupported']]);
});
