// Startup checks validate executable/configuration only, never proof/backend readiness.
'use strict';
const fs=require('node:fs/promises'),{constants}=require('node:fs'),{join}=require('node:path'),{spawn}=require('node:child_process'),{terminateTree}=require('./backend.cjs');
const {performance}=require('node:perf_hooks');
const startupError=(message,setting,cause)=>Object.assign(new Error(message,{cause}),{code:'STARTUP',setting});
const cancelled=()=>Object.assign(new Error('Startup cancelled'),{code:'CANCELLED'});
function runtimeVersion(executable,cwd,signal){
 return new Promise((resolve,reject)=>{
  if(signal?.aborted){reject(cancelled());return;}
  const child=spawn(executable,['--version'],{cwd,detached:process.platform!=='win32',windowsHide:true,shell:false,stdio:['ignore','pipe','pipe']});
  let stdout='',stderr='',finished=false;
  const finish=(error,value)=>{if(finished)return;finished=true;clearTimeout(timer);signal?.removeEventListener('abort',abort);error?reject(error):resolve(value);};
  const stop=error=>{terminateTree(child);finish(error);},abort=()=>stop(cancelled());
  const timer=setTimeout(()=>stop(startupError('Node.js version check timed out after 5000 ms','nodePath')),5000);
  signal?.addEventListener('abort',abort,{once:true});
  child.on('error',error=>finish(startupError('Cannot execute configured Node.js runtime: '+error.message,'nodePath',error)));
  child.stdout.on('data',chunk=>{stdout+=chunk;if(Buffer.byteLength(stdout)>65536)stop(startupError('Node.js version output exceeded 64 KiB','nodePath'));});
  child.stderr.on('data',chunk=>{stderr=(stderr+chunk).slice(-4000);});
  child.on('close',code=>{
   if(finished)return;const match=/^v(\d+\.\d+\.\d+(?:-[0-9A-Za-z.-]+)?)$/.exec(stdout.trim());
   if(code!==0||!match){finish(Object.assign(startupError('Cannot determine Node.js version (unknown): '+(stderr.trim()||stdout.trim()||'no version returned'),'nodePath'),{runtimeInfo:{configuredPath:executable,version:'unknown'}}));return;}
   const version=match[1],runtimeInfo={configuredPath:executable,version};
   // Existing supported-version contract: vscode/README.md Setup requires Node.js18+.
   if(Number(version.split('.')[0])<18){finish(Object.assign(startupError('Node.js '+version+' is unsupported; Solidity Lean requires Node.js18 or later','nodePath'),{runtimeInfo}));return;}
   finish(null,runtimeInfo);
  });
 });
}
async function checkStartup(configuration,signal){
 const root=configuration.backendPath;
 try{
  if(!(await fs.stat(root)).isDirectory())throw Error('Backend path is not a directory');
  await fs.access(root,constants.R_OK|constants.X_OK);
  for(const relative of ['scripts/test-solidity.mjs','lean-toolchain']){const file=join(root,relative);if(!(await fs.stat(file)).isFile())throw Error('Backend file is not a regular file: '+file);await fs.access(file,constants.R_OK);}
 }catch(cause){throw startupError('Solidity Lean backend is unavailable at '+root+': '+cause.message,'backendPath',cause);}
 if(signal?.aborted)throw cancelled();
 return runtimeVersion(configuration.nodePath||'node',root,signal);
}
function serverIdentity(value){return {name:typeof value?.name==='string'&&value.name.trim()?value.name.trim().slice(0,128):'unknown',version:typeof value?.version==='string'&&/^\d+\.\d+\.\d+(?:[-+][0-9A-Za-z.-]+)?$/.test(value.version)?value.version:'unknown'};}
// Local producer is the running server manifest, never a Dafny/Lean version or proof status.
const versionNotification='solidityLean/serverVersion',versionTimeoutMs=5000,versionCandidateLimit=128,versionMetadataLimit=65536;
function waitForServerVersion(peer,signal){
 let settled=false,started=false,initial,timer,deadline,resolve,reject,earlyBytes=0;const early=new Map();
 const promise=new Promise((yes,no)=>{resolve=yes;reject=no;});promise.catch(()=>{});
 const finish=(error,serverInfo,source)=>{if(settled)return;settled=true;early.clear();earlyBytes=0;clearTimeout(timer);registration.dispose();peer.removeListener('close',closed);signal?.removeEventListener('abort',abort);error?reject(error):resolve({serverInfo,source});};
 const valid=value=>value&&typeof value.name==='string'&&value.name.trim()&&value.name.length<=128&&typeof value.version==='string'&&value.version.length<=versionMetadataLimit&&serverIdentity(value).version!=='unknown';
 const accept=value=>{if(!valid(value))return;const identity=serverIdentity(value);if(initial.name!=='unknown'&&initial.name!==identity.name)return;if(performance.now()>=deadline){finish(null,initial,'timeout');return;}finish(null,identity,'notification');};
 const metadataError=()=>finish(startupError('Server version metadata exceeded 128 candidates or 64 KiB',null));
 const registration=peer.onNotification(versionNotification,value=>{
   if(settled)return;if(typeof value?.version==='string'&&value.version.length>versionMetadataLimit){metadataError();return;}if(!valid(value))return;
   const identity=serverIdentity(value),bytes=Buffer.byteLength(JSON.stringify(identity));if(bytes>versionMetadataLimit){metadataError();return;}
   if(!started){if(!early.has(identity.name)){if(early.size>=versionCandidateLimit||earlyBytes+bytes>versionMetadataLimit){metadataError();return;}early.set(identity.name,identity);earlyBytes+=bytes;}return;}accept(identity);
 });
 const closed=error=>finish(error||cancelled()),abort=()=>finish(cancelled());
 peer.on('close',closed);signal?.addEventListener('abort',abort,{once:true});
 if(signal?.aborted||peer.closed)finish(cancelled());
 return {promise,get pending(){return !settled;},start(info){
   if(!started&&!settled){started=true;initial={...serverIdentity(info),version:'unknown'};deadline=performance.now()+versionTimeoutMs;timer=setTimeout(()=>finish(null,initial,'timeout'),versionTimeoutMs);const candidate=initial.name==='unknown'?early.values().next().value:early.get(initial.name);early.clear();earlyBytes=0;if(candidate)accept(candidate);}
   return promise;
 },dispose(){finish(cancelled());}};
}
module.exports={checkStartup,runtimeVersion,serverIdentity,startupError,cancelled,versionNotification,versionTimeoutMs,versionCandidateLimit,versionMetadataLimit,waitForServerVersion};
