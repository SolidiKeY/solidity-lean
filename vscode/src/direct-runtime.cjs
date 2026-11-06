'use strict';
const fs=require('node:fs'),path=require('node:path'),{createHash}=require('node:crypto');
const {requestFor,decorate}=require('./direct-model.cjs');
const {spawn}=require('node:child_process');
const {createInterface}=require('node:readline');
const {machine}=require('node:os');
const loaded=new Map();let checks=0;
const sha=bytes=>createHash('sha256').update(bytes).digest('hex');
function candidates(root){return process.env.SOLIDITY_LEAN_DIRECT_DIR?[path.resolve(process.env.SOLIDITY_LEAN_DIRECT_DIR)]:[path.join(root,'.lake/direct-native'),path.join(root,'.lake/direct-runtime'),path.join(__dirname,'../runtime/native'),path.join(__dirname,'../runtime/direct')];}
function stamp(file){try{const s=fs.statSync(file,{bigint:true});return [s.dev,s.ino,s.size,s.mtimeNs,s.ctimeNs].map(String).join(':');}catch{return 'missing';}}
function directFingerprint(root){
 if(process.env.SOLIDITY_LEAN_DIRECT==='0')return 'disabled';
 const hash=createHash('sha256');
 hash.update(stamp(path.join(root,'web/browser/direct-bridge.c')));
 for(const dir of candidates(root)){
  hash.update(dir);for(const name of ['build.json','direct.js','direct.wasm','direct-check'])hash.update(stamp(path.join(dir,name)));
  try{const m=JSON.parse(fs.readFileSync(path.join(dir,'build.json'),'utf8'));for(const e of m.sourceFiles||[])hash.update(stamp(path.join(root,e.module.replaceAll('.','/')+'.lean')));}catch{}
 }
 return hash.digest('hex');
}
async function nativeRuntime(dir,manifest){
 const executable=path.join(dir,'direct-check');
 if(manifest.platform!==process.platform||manifest.arch!==machine()||sha(fs.readFileSync(executable))!==manifest.executable)return null;
 const start=performance.now(),child=spawn(executable,[],{stdio:['pipe','pipe','pipe'],windowsHide:true});
 let pending,failed=false;
 const close=()=>{failed=true;child.kill();};
 const fail=error=>{failed=true;pending?.reject(error);pending=undefined;child.kill();};
 const lines=createInterface({input:child.stdout});
 const next=()=>new Promise((resolve,reject)=>{pending={resolve,reject};});
 const boot=next();
 lines.on('line',line=>{const p=pending;pending=undefined;if(!p){fail(new Error('Unexpected compiled verifier output'));return;}try{p.resolve(JSON.parse(line));}catch(error){p.reject(error);close();}});
 child.on('error',fail);child.on('exit',()=>fail(new Error('Compiled verifier stopped')));
 child.stdin.on('error',fail);
 // Consume bounded diagnostic output without exposing it as protocol results.
 child.stderr.on('data',()=>{});
 let timer;try{
  const ready=await Promise.race([boot,new Promise((_,reject)=>{timer=setTimeout(()=>reject(new Error('Compiled verifier startup timed out')),10000);})]);
  if(ready.ready!==true)throw new Error('Invalid compiled verifier handshake');
 }catch(error){close();throw error;}finally{clearTimeout(timer);}
 return {manifest,bootMs:performance.now()-start,kind:'generated-c-native',close,async check(input){
  if(failed||pending)throw new Error('Compiled verifier is unavailable or busy');
  const result=next();child.stdin.write(JSON.stringify(input)+'\n',error=>{if(error)fail(error);});return result;
 }};
}
async function load(root){
 if(process.env.SOLIDITY_LEAN_DIRECT==='0')return null;
 const key=root+':'+directFingerprint(root);if(loaded.has(key))return loaded.get(key);
 const promise=(async()=>{
  for(const dir of candidates(root))try{
   const manifest=JSON.parse(fs.readFileSync(path.join(dir,'build.json'),'utf8'));
   if(manifest.version!==1||manifest.leanCommit!=='797c613eb9b6d4ec95db23e3e00af9ac6657f24b')continue;
   if(!Array.isArray(manifest.sourceFiles)||!manifest.sourceFiles.some(e=>e.module==='Solidity.Tools.DirectRuntime'))continue;
   if(manifest.toolchain!==fs.readFileSync(path.join(root,'lean-toolchain'),'utf8').trim())continue;
   if(manifest.bridgeSha256&&sha(fs.readFileSync(path.join(root,'web/browser/direct-bridge.c')))!==manifest.bridgeSha256)continue;
   if(!manifest.sourceFiles.every(e=>typeof e.sourceSha256==='string'&&sha(fs.readFileSync(path.join(root,e.module.replaceAll('.','/')+'.lean')))===e.sourceSha256))continue;
   if(manifest.executable){const native=await nativeRuntime(dir,manifest);if(native)return native;continue;}
   const wasm=fs.readFileSync(path.join(dir,'direct.wasm')),script=path.join(dir,'direct.js');
   if(sha(wasm)!==manifest.wasm||sha(fs.readFileSync(script))!==manifest.javascript)continue;
   delete require.cache[require.resolve(script)];const factory=require(script),start=performance.now();
   const module=await factory({wasmBinary:wasm,print:()=>{},printErr:()=>{}});
   if(module.ccall('direct_init','number',[],[])!==0)continue;
   return {module,manifest,bootMs:performance.now()-start,kind:'generated-c-wasm'};
  }catch{}
  return null;
 })();for(const previous of loaded.values())previous.then(runtime=>runtime?.close?.());loaded.clear();loaded.set(key,promise);return promise;
}
async function checkDirect(root,contract,options){
 const input=requestFor(contract,options);if(!input)return null;
 const runtime=await load(root);if(!runtime)return null;
 const start=performance.now();let result;
 try{result=runtime.check?await runtime.check(input):JSON.parse(runtime.module.ccall('direct_check','string',['string'],[JSON.stringify(input)]));}
 catch{runtime.close?.();loaded.clear();return null;}
 result=decorate(contract,result);if(!result)return null;
 return {...result,timings:{backend:runtime.kind,checkSequence:++checks,checkMs:performance.now()-start,environmentImports:0},build:runtime.manifest.wasm??runtime.manifest.executable,bootMs:runtime.bootMs};
}
module.exports={checkDirect,directFingerprint};
