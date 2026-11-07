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

// Guard cache ownership under old-result failure, superseded startup and terminal disposal.
// Native protocol/Wasm boundaries here are injected and return pending, never proof evidence.
function isolatedRuntime(onClose){
 const file=require.resolve('../src/direct-runtime.cjs'),original=require.cache[file],lifetime=require('../src/child-lifetime.cjs'),wait=lifetime.waitForClose;
 if(onClose)lifetime.waitForClose=(...args)=>onClose(wait,...args);delete require.cache[file];const api=require(file);lifetime.waitForClose=wait;
 return {api,restore(){if(original)require.cache[file]=original;else delete require.cache[file];}};
}
function nativeFixture(f,body){
 const program='#!'+process.execPath+'\n'+body,file=path.join(f.dir,'direct-check'),manifest=JSON.parse(fs.readFileSync(path.join(f.dir,'build.json'),'utf8'));
 fs.writeFileSync(file,program,{mode:0o700});Object.assign(manifest,{platform:process.platform,arch:os.machine(),executable:sha(program)});fs.writeFileSync(path.join(f.dir,'build.json'),JSON.stringify(manifest));
}
const pendingRow={sourceId:1,function:'f',status:'pending',verification:'direct',reason:'Injected lifecycle boundary only'};
const untilFixture=async predicate=>{const deadline=Date.now()+1000;while(!predicate()){assert.ok(Date.now()<deadline,'fixture boundary did not arrive');await new Promise(r=>setTimeout(r,2));}};
test('native cache retains newer entry after old check failure (injected protocol)',{skip:process.platform!=='linux'},async()=>{
 const f=fixture(),control=isolatedRuntime(),firstMarker=path.join(f.root,'first'),received=path.join(f.root,'received'),secondMarker=path.join(f.root,'second');let first;
 try{nativeFixture(f,`const fs=require('node:fs');fs.writeFileSync(${JSON.stringify(firstMarker)},String(process.pid));console.log('{"ready":true}');require('node:readline').createInterface({input:process.stdin}).on('line',()=>fs.writeFileSync(${JSON.stringify(received)},'request'));setInterval(()=>{},1000);`);first=control.api.checkDirect(f.root,f.contract,{}).catch(error=>error);await untilFixture(()=>fs.existsSync(received));const oldPid=Number(fs.readFileSync(firstMarker));
 nativeFixture(f,`const fs=require('node:fs');let count=0;let oldPresent;try{process.kill(${oldPid},0);oldPresent=true;}catch{oldPresent=false;}const write=()=>fs.writeFileSync(${JSON.stringify(secondMarker)},JSON.stringify({pid:process.pid,count,oldPresent}));write();console.log('{"ready":true}');require('node:readline').createInterface({input:process.stdin}).on('line',()=>{count++;write();console.log(${JSON.stringify(JSON.stringify({results:[pendingRow]}))});});setInterval(()=>{},1000);`);
 const second=await control.api.checkDirect(f.root,f.contract,{}),afterSecond=JSON.parse(fs.readFileSync(secondMarker));const oldResult=await first;const third=await control.api.checkDirect(f.root,f.contract,{}),afterThird=JSON.parse(fs.readFileSync(secondMarker));if(process.env.DAFNY_DIRECT_CACHE_EVIDENCE)fs.writeFileSync(process.env.DAFNY_DIRECT_CACHE_EVIDENCE,JSON.stringify({scope:'Injected pending-only native protocol; no kernel/C equivalence.',afterSecond,oldResult:oldResult instanceof Error?{error:oldResult.message}:oldResult,afterThird},null,2)+'\n');
 assert.equal(second.results[0].status,'pending');assert.equal(third.results[0].status,'pending');assert.equal(afterSecond.oldPresent,false,'replacement admitted before old physical close');assert.equal(afterThird.pid,afterSecond.pid,'old failure evicted newer runtime');assert.equal(afterThird.count,2);assert.ok(oldResult instanceof Error,'superseded check must reject');
 }finally{await control.api.disposeDirect();await first;control.restore();fs.rmSync(f.root,{recursive:true,force:true});}
});
test('native cache refuses admission superseded during retirement (injected confirmation gate)',{skip:process.platform!=='linux'},async()=>{
 let hold=false,release;const control=isolatedRuntime(async(wait,...args)=>{await wait(...args);if(hold){hold=false;await new Promise(resolve=>{release=resolve;});}}),f=fixture(),admissions=path.join(f.root,'admissions');let first,second;
 const program=label=>`require('node:fs').appendFileSync(${JSON.stringify(admissions)},JSON.stringify({pid:process.pid,label:${JSON.stringify(label)}})+'\\n');console.log('{"ready":true}');require('node:readline').createInterface({input:process.stdin}).on('line',()=>console.log(${JSON.stringify(JSON.stringify({results:[pendingRow]}))}));setInterval(()=>{},1000);`;
 try{nativeFixture(f,program('base'));await control.api.checkDirect(f.root,f.contract,{});hold=true;nativeFixture(f,program('superseded'));first=control.api.checkDirect(f.root,f.contract,{}).catch(error=>error);await untilFixture(()=>release);nativeFixture(f,program('current'));second=control.api.checkDirect(f.root,f.contract,{}).catch(error=>error);await new Promise(setImmediate);release();const a=await first,b=await second,rows=fs.readFileSync(admissions,'utf8').trim().split('\n').map(line=>JSON.parse(line));assert.ok(a instanceof Error,'superseded startup returned a result');assert.ok(!(b instanceof Error),b?.message);assert.deepEqual(rows.map(r=>r.label),['base','current'],'superseded startup admitted a child');}
 finally{release?.();await control.api.disposeDirect();await Promise.allSettled([first,second]);control.restore();fs.rmSync(f.root,{recursive:true,force:true});}
});
test('direct result cannot publish after terminal disposal (injected Wasm boundary)',async()=>{
 const f=fixture(),control=isolatedRuntime(),previous=globalThis.__directRetirementControl;try{const script="module.exports=async()=>({ccall:name=>name==='direct_init'?0:(globalThis.__directRetirementControl(),JSON.stringify({results:[{sourceId:1,function:'f',status:'pending',verification:'direct'}]}))});";fs.writeFileSync(path.join(f.dir,'direct.js'),script);const manifest=JSON.parse(fs.readFileSync(path.join(f.dir,'build.json'),'utf8'));manifest.javascript=sha(script);fs.writeFileSync(path.join(f.dir,'build.json'),JSON.stringify(manifest));globalThis.__directRetirementControl=()=>{control.api.disposeDirect();};await assert.rejects(control.api.checkDirect(f.root,f.contract,{}),/retiring|superseded/);}
 finally{await control.api.disposeDirect();if(previous===undefined)delete globalThis.__directRetirementControl;else globalThis.__directRetirementControl=previous;control.restore();fs.rmSync(f.root,{recursive:true,force:true});}
});
