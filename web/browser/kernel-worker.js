/* The pinned Lean kernel runs in its own disposable worker. No server RPC. */
'use strict';
import {gunzipSync} from 'fflate';
import {createSHA256} from 'hash-wasm';
import {prepareBrotli,inflateBrotli} from './brotli.mjs';
import {prepareZstd,inflateZstd} from './zstd.mjs';
let runtimePromise;
let hasher;
let inflate=bytes=>gunzipSync(bytes);
const diagnostics=[];
const stderr=[];
const metrics={reads:0,cacheHits:0,compressedBytes:0,inflatedBytes:0,fetchMs:0,hashMs:0,inflateMs:0,prefetchMs:0,prefetchedBytes:0,directReads:0,fallbacks:0};
const syncDigest=bytes=>hasher.init().update(bytes).digest('hex');
const sha256=async bytes=>globalThis.crypto?.subtle?Array.from(new Uint8Array(await crypto.subtle.digest('SHA-256',bytes)),b=>b.toString(16).padStart(2,'0')).join(''):syncDigest(bytes);
async function asset(entry){
  let buffer;
  if(globalThis.readEmbeddedAsset)buffer=await readEmbeddedAsset(entry.url);
  else{const response=await fetch(entry.url);if(!response.ok)throw new Error('Missing browser proof asset: '+entry.url);buffer=await response.arrayBuffer();}
  const bytes=new Uint8Array(buffer);
  if(await sha256(bytes)!==entry.sha256)throw new Error('Browser proof asset checksum mismatch: '+entry.url);
  return bytes;
}
async function binary(entry){
  const bytes=new Uint8Array(entry.size);let offset=0;
  for(const chunk of entry.chunks){const part=inflate(await asset(chunk),chunk.size);bytes.set(part,offset);offset+=part.length;}
  if(offset!==entry.size||await sha256(bytes)!==entry.sha256)throw new Error('Invalid Lean runtime binary');return bytes;
}
function mkdir(FS,path){const parts=path.split('/');parts.pop();let current='';for(const part of parts.filter(Boolean)){current+='/'+part;try{FS.mkdir(current);}catch(error){if(!FS.analyzePath(current).exists)throw error;}}}
async function boot(){
  hasher=await createSHA256();
  const response=await fetch('/lean/manifest.json');if(!response.ok)throw new Error('Pinned Lean browser runtime is missing');
  const manifest=await response.json();
  if(manifest.version!=='4.24.0'||manifest.commit!=='797c613eb9b6d4ec95db23e3e00af9ac6657f24b'||manifest.wordSize!==64||manifest.gmpBits!==64)throw new Error('Incompatible Lean browser runtime');
  if(manifest.compression==='brotli'){
    prepareBrotli(await (await fetch('/brotli-dec.wasm')).arrayBuffer());inflate=inflateBrotli;
  }else if(manifest.compression==='zstd'){
    await prepareZstd();inflate=inflateZstd;
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
  // a bounded 8 MiB set of modules to avoid reinflating header/body/IR reads.
  const libraryCache=new Map(),loadedLibraries=new Set(),prefetched=new Map();let libraryBytes=0,preparing,lastFile,lastContents;
  // Lean's synchronous file API otherwise makes thousands of blocking Blob/
  // HTTP requests. Fetch and authenticate compressed bytes concurrently, then
  // release each buffer as the importer consumes it. Never preload the several
  // GiB of decoded libraries into JS memory.
  const prepareLibraries=()=>preparing??= (async()=>{
    // In the self-contained build, owned Blobs support synchronous worker
    // reads directly. No network stack or bulk compressed prefetch is needed.
    if(globalThis.readEmbeddedAssetSync)return;
    const started=performance.now();let next=0,prefetchedBytes=0;
    await Promise.all(Array.from({length:8},async()=>{
      while(next<manifest.libraries.length){
        const chunk=manifest.libraries[next++];
        const bytes=await asset(chunk);
        // Bound retained compressed storage as well as decoder/cache storage.
        // Larger future manifests can use the checked synchronous fallback.
        if(prefetchedBytes+bytes.length<=768*1024*1024){prefetched.set(chunk.url,bytes);prefetchedBytes+=bytes.length;}
      }
    }));
    metrics.prefetchMs=performance.now()-started;
    metrics.prefetchedBytes=prefetchedBytes;
  })();
  const library=chunk=>{
    metrics.reads++;
    if(libraryCache.has(chunk.url)){metrics.cacheHits++;const bytes=libraryCache.get(chunk.url);libraryCache.delete(chunk.url);libraryCache.set(chunk.url,bytes);return bytes;}
    let started=performance.now();
    let compressed=prefetched.get(chunk.url);
    if(compressed)prefetched.delete(chunk.url);
    else{
      if(globalThis.readEmbeddedAssetSync){metrics.directReads++;compressed=new Uint8Array(readEmbeddedAssetSync(chunk.url));}
      else{
        metrics.fallbacks++;
        const request=new XMLHttpRequest();request.open('GET',chunk.url,false);request.responseType='arraybuffer';request.send();
        if(request.status!==200)throw new Error('Missing offline Lean library: '+chunk.url);
        compressed=new Uint8Array(request.response);
      }
      metrics.fetchMs+=performance.now()-started;
      const hashStarted=performance.now();
      if(syncDigest(compressed)!==chunk.sha256)throw new Error('Lean library checksum mismatch: '+chunk.url);
      metrics.hashMs+=performance.now()-hashStarted;
    }
    metrics.compressedBytes+=compressed.length;started=performance.now();
    const bytes=inflate(compressed,chunk.size);if(bytes.length!==chunk.size)throw new Error('Invalid Lean library size');
    metrics.inflateMs+=performance.now()-started;metrics.inflatedBytes+=bytes.length;
    if(!loadedLibraries.has(chunk.url)){loadedLibraries.add(chunk.url);postMessage({method:'progress',loaded:loadedLibraries.size,total:manifest.libraries.length,module:chunk.files[0].path});}
    libraryCache.set(chunk.url,bytes);libraryBytes+=bytes.length;
    while(libraryBytes>8*1024*1024&&libraryCache.size>1){const oldest=libraryCache.keys().next().value;libraryBytes-=libraryCache.get(oldest).length;libraryCache.delete(oldest);}
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
      // std::ifstream reads a file in many small pieces. Retain just one view
      // across consecutive reads, rather than allocating a view and updating
      // the LRU over a million times. A view per node would pin every library.
      Object.defineProperty(node,'contents',{get:()=>{
        if(lastFile!==file){lastContents=library(chunk).subarray(file.offset,file.offset+file.size);lastFile=file;}
        return lastContents;
      }});
    }
  }
  for(const path of ['/workspace','/output','/bin'])try{Module.FS.mkdir(path);}catch{}
  Module.FS.chdir('/workspace');
  if(Module.ccall('browser_init','number',[],[])!==0)throw new Error('Lean kernel initialization failed');
  if(Module.ccall('browser_promise_probe','number',[],[])!==0)throw new Error('Lean synchronous promise startup test failed');
  if(Module.ccall('browser_kernel_probe','number',[],[])!==0)throw new Error('Lean kernel declaration startup test failed');
  return {Module,manifest,prepareLibraries,releasePrefetched:()=>prefetched.clear()};
}
onmessage=async event=>{
  const {id,method,params={}}=event.data;
  try{
    runtimePromise??=boot();const {Module,manifest,prepareLibraries,releasePrefetched}=await runtimePromise;
    if(method==='boot'){postMessage({id,result:{version:manifest.version,build:manifest.build}});return;}
    if(method!=='check')throw new Error('Unknown kernel operation');
    const started=performance.now();
    const previous={...metrics};
    await prepareLibraries();
    diagnostics.length=0;stderr.length=0;
    for(const [path,text]of Object.entries(params.files||{})){
      if(!path.startsWith('/workspace/')||path.includes('..')||typeof text!=='string')throw new Error('Invalid proof input');
      mkdir(Module.FS,path);Module.FS.writeFile(path,text);
    }
    for(const path of params.outputs||[]){if(!path.startsWith('/output/')||path.includes('..'))throw new Error('Invalid proof output');try{Module.FS.unlink(path);}catch{}}
    let code;
    try{code=Module.ccall('browser_check','number',['string','string'],[params.source,'/workspace/BrowserCheck.lean']);}finally{releasePrefetched();}
    const outputs={};for(const path of params.outputs||[])if(Module.FS.analyzePath(path).exists){try{outputs[path]=Module.FS.readFile(path,{encoding:'utf8'});}finally{Module.FS.unlink(path);}}
    const libraries=Object.fromEntries(Object.entries(metrics).map(([key,value])=>[key,value-previous[key]]));
    postMessage({id,result:{code,diagnostics:diagnostics.splice(0),stderr:stderr.splice(0),outputs,timings:{checkMs:performance.now()-started,libraries}}});
  }catch(error){
    const stackLimit=(error instanceof RangeError||error instanceof WebAssembly.RuntimeError)&&/maximum call stack|call stack exhausted|too much recursion/i.test(error.message);
    postMessage({id,error:{message:stackLimit?'Browser proof checking exceeded its call-stack limit. No proof result was accepted.':error.message||String(error),code:stackLimit?'BROWSER_STACK_LIMIT':undefined,stack:error.stack,stderr:stderr.slice()}});
  }
};
