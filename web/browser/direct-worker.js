'use strict';
import {digest} from './digest.mjs';
let runtime,checks=0;
async function boot(){
  const manifest=await (await fetch('/direct/build.json')).json();
  if(manifest.version!==1||manifest.leanCommit!=='797c613eb9b6d4ec95db23e3e00af9ac6657f24b')throw new Error('Incompatible direct verifier');
  const bytes=async(path,expected)=>{
    const data=await(await fetch(path)).arrayBuffer();
    const hash=await digest(data);
    if(hash!==expected)throw new Error('Mismatched direct verifier asset');return data;
  };
  const [js,wasm]=await Promise.all([bytes('/direct/direct.js',manifest.javascript),bytes('/direct/direct.wasm',manifest.wasm)]);
  const factory=(0,eval)(new TextDecoder().decode(js)+';createDirectVerifier');
  const module=await factory({wasmBinary:wasm,print:()=>{},printErr:message=>postMessage({method:'log',message})});
  if(module.ccall('direct_init','number',[],[])!==0)throw new Error('Direct verifier initialization failed');
  return {module,manifest};
}
onmessage=async({data:{id,method,params={}}})=>{
  try{
    const {module,manifest}=await(runtime??=boot());
    if(method==='boot'){postMessage({id,result:{version:'4.24.0',kind:'generated-c-wasm',build:manifest.wasm,wasmBytes:manifest.wasmBytes}});return;}
    if(method!=='check')throw new Error('Unknown direct verifier operation');
    const started=performance.now();
    const value=module.ccall('direct_check','string',['string'],[JSON.stringify(params)]);
    postMessage({id,result:{...JSON.parse(value),timings:{checkSequence:++checks,checkMs:performance.now()-started,environmentImports:0,backend:'generated-c-wasm'}}});
  }catch(error){postMessage({id,error:{message:error.message,stack:error.stack}});}
};
