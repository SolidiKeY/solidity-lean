'use strict';
const {test}=require('node:test');
const assert=require('node:assert/strict');
const fs=require('node:fs');
const {join,resolve}=require('node:path');
const {tmpdir}=require('node:os');
const {createHash}=require('node:crypto');
const {inspectNative,nativeFingerprint}=require('../src/native-plugin.cjs');
const {LeanSession}=require('../src/lean-session.cjs');
const digest=bytes=>createHash('sha256').update(bytes).digest('hex');
const commit='1'.repeat(40),stem='Solidity/Frontend/Testing';
function fixture(){
  const root=fs.mkdtempSync(join(tmpdir(),'solidity-native-')),directory=join(root,'.lake/frontend-native');
  const put=(file,value)=>{fs.mkdirSync(require('node:path').dirname(join(root,file)),{recursive:true});fs.writeFileSync(join(root,file),value);};
  put('lean-toolchain','leanprover/lean4:v4.24.0\n');
  put('.lake/build/ir/'+stem+'.setup.json',JSON.stringify({importArts:{}}));
  const files={};
  for(const file of [stem+'.lean','.lake/build/ir/'+stem+'.c',...['.olean','.olean.private','.olean.server','.ir'].map(e=>'.lake/build/lib/lean/'+stem+e)]){put(file,'fixture '+file);files[file]=digest(fs.readFileSync(join(root,file)));}
  const bytes=Buffer.from('native fixture'),sha256=digest(bytes),pluginFile=`${sha256}/libSolidity_Frontend_Testing.so`;
  put('.lake/frontend-native/'+pluginFile,bytes);
  const manifest={schemaVersion:1,platform:process.platform,architecture:process.arch,toolchain:'leanprover/lean4:v4.24.0',leanCommit:commit,optimization:'-O0',nativeProbe:false,
    modules:[{module:'Solidity.Frontend.Testing',sourceCSha256:files['.lake/build/ir/'+stem+'.c'],cSha256:files['.lake/build/ir/'+stem+'.c'],files}],pluginSha256:sha256,pluginFile};
  manifest.modules[0].fileStats=Object.fromEntries(Object.keys(files).map(file=>{const s=fs.statSync(join(root,file),{bigint:true});return [file,[s.dev,s.ino,s.size,s.mtimeNs,s.ctimeNs].map(String)];}));
  const publish=()=>put('.lake/frontend-native/build.json',JSON.stringify(manifest));publish();
  return {root,directory,put,manifest,publish,cleanup:()=>fs.rmSync(root,{recursive:true,force:true})};
}

test('native selection checks runtime identity and every source/artifact variant',()=>{
  for(const mutate of [f=>f.manifest.architecture='wrong',f=>f.manifest.toolchain='wrong',f=>f.manifest.schemaVersion=0,
    f=>f.manifest.modules=[],f=>f.manifest.modules[0].sourceCSha256='wrong',f=>f.manifest.modules[0].cSha256='wrong',f=>f.manifest.pluginFile='../other.so']){
    const f=fixture();try{assert.ok(inspectNative(f.root,{env:{}}).path);mutate(f);f.publish();assert.equal(inspectNative(f.root,{env:{}}).path,undefined);}finally{f.cleanup();}
  }
  for(const file of [stem+'.lean','.lake/build/ir/'+stem+'.c',...['.olean','.olean.private','.olean.server','.ir'].map(e=>'.lake/build/lib/lean/'+stem+e)]){
    const f=fixture();try{const before=nativeFingerprint(f.root,{});f.put(file,'changed');assert.equal(inspectNative(f.root,{env:{}}).reason,'stale');assert.notEqual(nativeFingerprint(f.root,{}),before);}finally{f.cleanup();}
  }
});
test('missing, disabled, corrupt and replaced native libraries safely invalidate selection',()=>{
  const f=fixture();try{
    assert.equal(inspectNative(f.root,{env:{SOLIDITY_LEAN_NATIVE:'0'}}).reason,'disabled');
    const before=nativeFingerprint(f.root,{});f.put('.lake/frontend-native/'+f.manifest.pluginFile,'corrupt');
    assert.equal(inspectNative(f.root,{env:{}}).reason,'stale');assert.notEqual(nativeFingerprint(f.root,{}),before);
    fs.unlinkSync(join(f.directory,'build.json'));assert.equal(inspectNative(f.root,{env:{}}).reason,'not-built');
  }finally{f.cleanup();}
});

async function sessionFixture(mode,run){
  const f=fixture(),saved={};
  for(const key of ['SOLIDITY_LEAN_NATIVE','SOLIDITY_LEAN_NATIVE_DIR']){saved[key]=process.env[key];delete process.env[key];}
  const fake=join(f.root,'fake-lake.cjs'),rpc=resolve(__dirname,'../src/rpc.cjs');
  f.put('fake-mode.json',JSON.stringify(mode));
  f.put('fake-lake.cjs',`#!/usr/bin/env node
const fs=require('node:fs'),path=require('node:path');
const root=${JSON.stringify(f.root)},mode=JSON.parse(fs.readFileSync(path.join(root,'fake-mode.json')));
if(process.argv[2]==='env'){setTimeout(()=>console.log(mode.commit||${JSON.stringify(commit)}),mode.probeDelay||0);}
else{
 const native=process.argv.some(a=>a.startsWith('--plugin='));fs.appendFileSync(path.join(root,'launches.jsonl'),JSON.stringify({native})+'\\n');
 const {RpcPeer,failure}=require(${JSON.stringify(rpc)});const peer=new RpcPeer(process.stdin,process.stdout);let checks=0;
 peer.onRequest('initialize',()=>{
  if(native&&mode.dieInit){setTimeout(()=>process.exit(42),mode.dieInit);return new Promise(()=>{});}
  if(mode.hangInit)return new Promise(()=>{});return {capabilities:{}};
 });
 peer.onNotification('textDocument/didOpen',p=>fs.appendFileSync(path.join(root,'documents.jsonl'),JSON.stringify({native,version:p.textDocument.version})+'\\n'));
 peer.onRequest('textDocument/waitForDiagnostics',()=>{
  checks++;
  if(native&&mode.dieCheck){process.exit(42);return;}
  if(native&&checks===1&&mode.rpcError)throw failure('ordinary request error');
  if(native&&checks===1&&mode.timeout)return new Promise(()=>{});
  return {diagnostics:[]};
 });
}
`);
  fs.chmodSync(fake,0o755);
  f.put('scripts/lake-command.mjs',`export function lakeCommand(){return ${JSON.stringify(fake)}}`);
  const session=new LeanSession(f.root,join(f.root,'worker'));
  const rows=name=>fs.existsSync(join(f.root,name))?fs.readFileSync(join(f.root,name),'utf8').trim().split('\n').map(JSON.parse):[];
  try{await run(session,rows);}finally{session.dispose();f.cleanup();for(const [k,v] of Object.entries(saved)){if(v===undefined)delete process.env[k];else process.env[k]=v;}}
}

test('native initialization and in-flight crashes fall back once and reopen version1',async()=>{
  for(const mode of [{dieInit:10},{dieCheck:true}])await sessionFixture(mode,async(s,rows)=>{
    assert.deepEqual(await s.check('-- document',3000),[]);assert.equal(s.native.active,false);assert.equal(s.native.reason,'native-process-failed');assert.equal(s.version,1);
    assert.deepEqual(rows('launches.jsonl'),[{native:true},{native:false}]);
    assert.equal(rows('documents.jsonl').at(-1).version,1);
  });
});
test('ordinary RPC failures and timeouts keep a healthy native process enabled',async()=>{
  for(const mode of [{rpcError:true},{timeout:true}])await sessionFixture(mode,async(s,rows)=>{
    // Initialize separately so this exercises a check timeout rather than process startup.
    await s.start(3000);await assert.rejects(s.check('-- first',100),/ordinary request error|timed out/);
    assert.equal(s.native.active,true);assert.equal(s.nativeDisabled,undefined);
    assert.deepEqual(await s.check('-- next',3000),[]);assert.equal(s.version,2);assert.equal(rows('launches.jsonl').length,1);
  });
});
test('runtime mismatch avoids native loading and startup shares the original deadline',async()=>{
  await sessionFixture({commit:'2'.repeat(40)},async(s,rows)=>{
    assert.deepEqual(await s.check('-- document',3000),[]);assert.equal(s.native.reason,'runtime-mismatch');assert.deepEqual(rows('launches.jsonl'),[{native:false}]);
  });
  await sessionFixture({probeDelay:250,hangInit:true},async(s)=>{
    const start=performance.now();await assert.rejects(s.check('-- document',400),/timed out/);assert.ok(performance.now()-start<575,'startup granted a second timeout after the runtime probe');
  });
});
