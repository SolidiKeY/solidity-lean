#!/usr/bin/env node
// Guards against independently replaying stale .lake/build objects after Lake
// selected current cached artifacts. Only the fresh setup's exact import objects
// and traced public object are exposed to the checker; no project-path fallback.
import {readFileSync,writeFileSync,readdirSync,mkdirSync,mkdtempSync,existsSync,rmSync} from 'node:fs';
import {join,dirname,resolve} from 'node:path';
import {createHash} from 'node:crypto';
import {execFileSync} from 'node:child_process';
import {pathToFileURL} from 'node:url';
import {configuredCacheDir} from './trust-closure.mjs';
const extensions=['.olean.private','.olean.server','.olean'];
const digest=bytes=>createHash('sha256').update(bytes).digest('hex');
export function makeReplayInputs({setup,trace,cacheDir,destination,head='fixture',provenance=null}) {
 if(setup.name!=='Solidity.Theorems'||!setup.importArts||typeof setup.importArts!=='object')throw Error('invalid public setup');
 if(existsSync(destination))throw Error('replay destination already exists');
 mkdirSync(destination,{recursive:true});
 const files=new Map();
 function place(module,source) {
  if(!/^[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*$/u.test(module))throw Error('invalid replay module');
  const ext=extensions.find(e=>source.endsWith(e));
  if(!ext||!existsSync(source))throw Error(`current object unavailable: ${module}: ${source}`);
  const relative=module.replaceAll('.','/')+ext,bytes=readFileSync(source),sha256=digest(bytes);
  if(files.has(relative)){if(files.get(relative).sha256!==sha256)throw Error(`conflicting object: ${relative}`);return;}
  const target=join(destination,relative);mkdirSync(dirname(target),{recursive:true});
  writeFileSync(target,bytes,{flag:'wx',mode:0o444});
  files.set(relative,{path:relative,source:resolve(source),sha256,bytes:bytes.length});
 }
 try {
  for(const [module,paths] of Object.entries(setup.importArts)) {
   if(!Array.isArray(paths)||!paths.length)throw Error(`empty import objects: ${module}`);
   for(const path of paths)place(module,path);
  }
  const raw=trace.outputs?.o,hashes=typeof raw==='string'?[raw]:raw;
  if(!Array.isArray(hashes)||!hashes.length||hashes.some(h=>typeof h!=='string'))throw Error('public object trace missing');
  const artifacts=readdirSync(join(cacheDir,'artifacts'));
  for(const hash of hashes) {
   const matches=artifacts.filter(n=>n.startsWith(hash+'.')&&extensions.some(e=>n.endsWith(e)));
   if(!matches.length)throw Error(`current public artifact unavailable: ${hash}`);
   for(const name of matches)place('Solidity.Theorems',join(cacheDir,'artifacts',name));
  }
  if(!files.has('Solidity/Theorems.olean'))throw Error('public root not materialized');
  const manifest={schema:1,head,root:'Solidity.Theorems',provenance,scope:'fresh setup import objects and current traced root; source type closure is not the proof replay domain',files:[...files.values()].sort((a,b)=>a.path.localeCompare(b.path))};
  writeFileSync(join(destination,'MANIFEST.json'),JSON.stringify(manifest,null,2)+'\n');
  return manifest;
 } catch(error){rmSync(destination,{recursive:true,force:true});throw error;}
}
// A cache-hit build does not refresh the persisted .setup.json. Ask Lake's
// current graph resolver for setup every time, then bind that to the current
// root trace and source; never read the persisted setup as provenance.
export function currentReplayConfig({root=process.cwd(),run=execFileSync}={}) {
 const env={...process.env,LEAN_NUM_THREADS:'1'};
 run('lake',['build','Solidity.Theorems'],{cwd:root,env,stdio:['ignore','inherit','inherit'],timeout:3600000});
 const fresh=run('lake',['setup-file','Solidity/Theorems.lean'],{cwd:root,env,encoding:'utf8',timeout:300000,maxBuffer:64*1024*1024});
 const setup=JSON.parse(fresh);
 if(setup.name!=='Solidity.Theorems'||!setup.importArts)throw Error('fresh public setup unavailable');
 for(const [module,paths] of Object.entries(setup.importArts)) {
  if(!Array.isArray(paths)||!paths.every(p=>typeof p==='string'))throw Error(`invalid fresh imports: ${module}`);
  setup.importArts[module]=paths.map(p=>resolve(root,p));
 }
 const traceBytes=readFileSync(join(root,'.lake/build/lib/lean/Solidity/Theorems.trace'));
 const sourceBytes=readFileSync(join(root,'Solidity/Theorems.lean'));
 return {setup,trace:JSON.parse(traceBytes),provenance:{setupOrigin:'lake setup-file Solidity/Theorems.lean',
  setupSha256:digest(Buffer.from(fresh)),rootTraceSha256:digest(traceBytes),rootSourceSha256:digest(sourceBytes)}};
}
function main() {
 const {setup,trace,provenance}=currentReplayConfig();
 const parent='.lake/refactor-cache';mkdirSync(parent,{recursive:true});
 const directory=mkdtempSync(join(parent,'trust-replay-')),destination=join(directory,'inputs');
 const head=execFileSync('git',['rev-parse','HEAD'],{encoding:'utf8'}).trim();
 const manifest=makeReplayInputs({setup,trace,cacheDir:configuredCacheDir(),destination,head,provenance});
 console.error(`replay-inputs: ${manifest.files.length} current objects; manifest ${join(destination,'MANIFEST.json')}`);
 console.log(resolve(destination));
}
if(process.argv[1]&&import.meta.url===pathToFileURL(process.argv[1]).href)try{main();}catch(error){console.error(error.message);process.exitCode=1;}
