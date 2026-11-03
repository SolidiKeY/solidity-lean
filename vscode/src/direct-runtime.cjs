'use strict';
const fs=require('node:fs'),path=require('node:path'),{createHash}=require('node:crypto');
const {requestFor,decorate}=require('./direct-model.cjs');
const loaded=new Map();let checks=0;
const sha=bytes=>createHash('sha256').update(bytes).digest('hex');
function candidates(root){return process.env.SOLIDITY_LEAN_DIRECT_DIR?[path.resolve(process.env.SOLIDITY_LEAN_DIRECT_DIR)]:[path.join(root,'.lake/direct-runtime'),path.join(__dirname,'../runtime/direct')];}
function stamp(file){try{const s=fs.statSync(file,{bigint:true});return [s.dev,s.ino,s.size,s.mtimeNs,s.ctimeNs].map(String).join(':');}catch{return 'missing';}}
function directFingerprint(root){
 if(process.env.SOLIDITY_LEAN_DIRECT==='0')return 'disabled';
 const hash=createHash('sha256');
 for(const dir of candidates(root)){
  hash.update(dir);for(const name of ['build.json','direct.js','direct.wasm'])hash.update(stamp(path.join(dir,name)));
  try{const m=JSON.parse(fs.readFileSync(path.join(dir,'build.json'),'utf8'));for(const e of m.sourceFiles||[])hash.update(stamp(path.join(root,e.module.replaceAll('.','/')+'.lean')));}catch{}
 }
 return hash.digest('hex');
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
   if(!manifest.sourceFiles.every(e=>typeof e.sourceSha256==='string'&&sha(fs.readFileSync(path.join(root,e.module.replaceAll('.','/')+'.lean')))===e.sourceSha256))continue;
   const wasm=fs.readFileSync(path.join(dir,'direct.wasm')),script=path.join(dir,'direct.js');
   if(sha(wasm)!==manifest.wasm||sha(fs.readFileSync(script))!==manifest.javascript)continue;
   delete require.cache[require.resolve(script)];const factory=require(script),start=performance.now();
   const module=await factory({wasmBinary:wasm,print:()=>{},printErr:()=>{}});
   if(module.ccall('direct_init','number',[],[])!==0)continue;
   return {module,manifest,bootMs:performance.now()-start};
  }catch{}
  return null;
 })();loaded.clear();loaded.set(key,promise);return promise;
}
async function checkDirect(root,contract,options){
 const input=requestFor(contract,options);if(!input)return null;
 const runtime=await load(root);if(!runtime)return null;
 const start=performance.now();let result;
 try{result=JSON.parse(runtime.module.ccall('direct_check','string',['string'],[JSON.stringify(input)]));}
 catch{loaded.clear();return null;}
 result=decorate(contract,result);if(!result)return null;
 return {...result,timings:{backend:'generated-c-wasm',checkSequence:++checks,checkMs:performance.now()-start,environmentImports:0},build:runtime.manifest.wasm,bootMs:runtime.bootMs};
}
module.exports={checkDirect,directFingerprint};
