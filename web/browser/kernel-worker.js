/* The pinned Lean kernel runs in its own disposable worker. No server RPC. */
'use strict';
import {gunzipSync} from 'fflate';
import {sha256 as digest} from '@noble/hashes/sha256';
import {prepareBrotli,inflateBrotli} from './brotli.mjs';
let runtimePromise;
let inflate=bytes=>gunzipSync(bytes);
const diagnostics=[];
const stderr=[];
const sha256=async bytes=>Array.from(new Uint8Array(await crypto.subtle.digest('SHA-256',bytes)),b=>b.toString(16).padStart(2,'0')).join('');
async function asset(entry){
  const response=await fetch(entry.url);if(!response.ok)throw new Error('Missing browser proof asset: '+entry.url);
  const bytes=new Uint8Array(await response.arrayBuffer());
  if(await sha256(bytes)!==entry.sha256)throw new Error('Browser proof asset checksum mismatch: '+entry.url);
  return bytes;
}
async function binary(entry){
  const bytes=new Uint8Array(entry.size);let offset=0;
  for(const chunk of entry.chunks){const part=inflate(await asset(chunk));bytes.set(part,offset);offset+=part.length;}
  if(offset!==entry.size||await sha256(bytes)!==entry.sha256)throw new Error('Invalid Lean runtime binary');return bytes;
}
function mkdir(FS,path){const parts=path.split('/');parts.pop();let current='';for(const part of parts.filter(Boolean)){current+='/'+part;try{FS.mkdir(current);}catch(error){if(!FS.analyzePath(current).exists)throw error;}}}
async function boot(){
  const response=await fetch('/lean/manifest.json');if(!response.ok)throw new Error('Pinned Lean browser runtime is missing');
  const manifest=await response.json();
  if(manifest.version!=='4.24.0'||manifest.commit!=='797c613eb9b6d4ec95db23e3e00af9ac6657f24b'||manifest.wordSize!==64||manifest.gmpBits!==64)throw new Error('Incompatible Lean browser runtime');
  if(manifest.compression==='brotli'){
    prepareBrotli(await (await fetch('/brotli-dec.wasm')).arrayBuffer());inflate=inflateBrotli;
  }else if(manifest.compression&&manifest.compression!=='gzip')throw new Error('Unsupported Lean library compression');
  let js=await binary(manifest.javascript),wasm=await binary(manifest.wasm);
  // One instance owns this dedicated worker. Global script execution permits
  // Emscripten's compact export loop instead of 160,000 individual JS variables.
  const Module=await new Promise((resolve,reject)=>{
    globalThis.Module={noInitialRun:true,
      instantiateWasm(imports,receive){WebAssembly.instantiate(wasm,imports).then(({instance,module})=>{wasm=undefined;receive(instance,module);}).catch(reject);return {};},
      onRuntimeInitialized:()=>resolve(globalThis.Module),onAbort:message=>reject(new Error(String(message))),
      print:line=>{try{const row=JSON.parse(line);if(row.severity)diagnostics.push(row);}catch{}},
      printErr:line=>{stderr.push(String(line).slice(-2000));if(stderr.length>20)stderr.shift();postMessage({method:'log',message:String(line).slice(-2000)});}};
    try{(0,eval)(new TextDecoder().decode(js));}catch(error){reject(error);}finally{js=undefined;}
  });
  if(Module.ccall('browser_identity','string',[],[])!=='4.24.0|797c613eb9b6d4ec95db23e3e00af9ac6657f24b|64|64')throw new Error('Loaded kernel identity or library layout does not match the pin');
  // Lean's imports are synchronous. Libraries are immutable same-origin static
  // assets, cached in full by the service worker before offline use. Inflate only
  // a bounded 64 MiB set of modules to avoid reinflating header/body/IR reads.
  const libraryCache=new Map(),loadedLibraries=new Set();let libraryBytes=0;
  const library=chunk=>{
    if(libraryCache.has(chunk.url)){const bytes=libraryCache.get(chunk.url);libraryCache.delete(chunk.url);libraryCache.set(chunk.url,bytes);return bytes;}
    const request=new XMLHttpRequest();request.open('GET',chunk.url,false);request.responseType='arraybuffer';request.send();
    if(request.status!==200)throw new Error('Missing offline Lean library: '+chunk.url);
    const compressed=new Uint8Array(request.response);
    const actual=Array.from(digest(compressed),b=>b.toString(16).padStart(2,'0')).join('');
    if(actual!==chunk.sha256)throw new Error('Lean library checksum mismatch: '+chunk.url);
    const bytes=inflate(compressed,chunk.size);if(bytes.length!==chunk.size)throw new Error('Invalid Lean library size');
    if(!loadedLibraries.has(chunk.url)){loadedLibraries.add(chunk.url);postMessage({method:'progress',loaded:loadedLibraries.size,total:manifest.libraries.length,module:chunk.files[0].path});}
    libraryCache.set(chunk.url,bytes);libraryBytes+=bytes.length;
    while(libraryBytes>64*1024*1024&&libraryCache.size>1){const oldest=libraryCache.keys().next().value;libraryBytes-=libraryCache.get(oldest).length;libraryCache.delete(oldest);}
    return bytes;
  };
  for(const chunk of manifest.libraries){
    for(const file of chunk.files){
      if(!file.path.startsWith('/lib/lean/')||file.path.includes('..')||!Number.isSafeInteger(file.offset)||!Number.isSafeInteger(file.size)||file.offset<0||file.size<0||file.offset+file.size>chunk.size)throw new Error('Invalid Lean library manifest');
      mkdir(Module.FS,file.path);
      const split=file.path.lastIndexOf('/');
      Module.FS.createDataFile(file.path.slice(0,split),file.path.slice(split+1),new Uint8Array(),true,false);
      const node=Module.FS.lookupPath(file.path).node;
      node.usedBytes=file.size;
      Object.defineProperty(node,'contents',{get:()=>library(chunk).subarray(file.offset,file.offset+file.size)});
    }
  }
  for(const path of ['/workspace','/output','/bin'])try{Module.FS.mkdir(path);}catch{}
  Module.FS.chdir('/workspace');
  if(Module.ccall('browser_init','number',[],[])!==0)throw new Error('Lean kernel initialization failed');
  if(Module.ccall('browser_promise_probe','number',[],[])!==0)throw new Error('Lean synchronous promise startup test failed');
  if(Module.ccall('browser_kernel_probe','number',[],[])!==0)throw new Error('Lean kernel declaration startup test failed');
  return {Module,manifest};
}
onmessage=async event=>{
  const {id,method,params={}}=event.data;
  try{
    runtimePromise??=boot();const {Module,manifest}=await runtimePromise;
    if(method==='boot'){postMessage({id,result:{version:manifest.version,build:manifest.build}});return;}
    if(method!=='check')throw new Error('Unknown kernel operation');
    diagnostics.length=0;stderr.length=0;
    for(const [path,text]of Object.entries(params.files||{})){
      if(!path.startsWith('/workspace/')||path.includes('..')||typeof text!=='string')throw new Error('Invalid proof input');
      mkdir(Module.FS,path);Module.FS.writeFile(path,text);
    }
    for(const path of params.outputs||[]){if(!path.startsWith('/output/')||path.includes('..'))throw new Error('Invalid proof output');try{Module.FS.unlink(path);}catch{}}
    const code=Module.ccall('browser_check','number',['string','string'],[params.source,'/workspace/BrowserCheck.lean']);
    const outputs={};for(const path of params.outputs||[])if(Module.FS.analyzePath(path).exists){try{outputs[path]=Module.FS.readFile(path,{encoding:'utf8'});}finally{Module.FS.unlink(path);}}
    postMessage({id,result:{code,diagnostics:diagnostics.splice(0),stderr:stderr.splice(0),outputs}});
  }catch(error){postMessage({id,error:{message:error.message||String(error),stack:error.stack,stderr:stderr.slice()}});}
};
