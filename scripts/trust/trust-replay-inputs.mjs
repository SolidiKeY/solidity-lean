#!/usr/bin/env node
// Guards against independently replaying stale .lake/build objects after Lake
// selected current cached artifacts. Only the fresh setup's exact import objects
// including the public root are exposed to the checker; no trace/path fallback.
import {readFileSync,writeFileSync,mkdirSync,mkdtempSync,existsSync,rmSync} from 'node:fs';
import {join,dirname,resolve} from 'node:path';
import {createHash} from 'node:crypto';
import {execFileSync} from 'node:child_process';
import {pathToFileURL} from 'node:url';
import {freshArtifactGraph} from './trust-artifacts.mjs';
const extensions=['.olean.private','.olean.server','.olean'];
const digest=bytes=>createHash('sha256').update(bytes).digest('hex');
export function makeReplayInputs({imports,destination,head='fixture',provenance=null}) {
 if(!imports||typeof imports!=='object'||!Array.isArray(imports['Solidity.Theorems'])||!imports['Solidity.Theorems'].length)throw Error('current public root unavailable');
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
  for(const [module,paths] of Object.entries(imports)) {
   if(!Array.isArray(paths)||!paths.length)throw Error(`empty import objects: ${module}`);
   for(const path of paths)place(module,path);
  }
  if(!files.has('Solidity/Theorems.olean'))throw Error('public root not materialized');
  const manifest={schema:1,head,root:'Solidity.Theorems',provenance,scope:'fresh importing setup selects every object including the public root; source type closure is not the proof replay domain',files:[...files.values()].sort((a,b)=>a.path.localeCompare(b.path))};
  writeFileSync(join(destination,'MANIFEST.json'),JSON.stringify(manifest,null,2)+'\n');
  return manifest;
 } catch(error){rmSync(destination,{recursive:true,force:true});throw error;}
}
// Cache hits leave persisted setup and trace files stale. Resolve the root
// itself as an import, so every copied object is selected by the current graph.
export function currentReplayConfig({root=process.cwd(),run=execFileSync}={}) {
 const env={...process.env,LEAN_NUM_THREADS:'1'};
 // The CLI reserves stdout for one directory; Lake prints build summaries.
 run('lake',['build','Solidity.Theorems'],{cwd:root,env,stdio:['ignore',2,2],timeout:3600000});
 const graph=freshArtifactGraph('Solidity.Theorems',{root,run});
 return {imports:graph.imports,provenance:{setupOrigin:graph.origin,setupSha256:graph.querySha256,
  rootSourceSha256:digest(readFileSync(join(root,'Solidity/Theorems.lean')))}};
}
function main() {
 const {imports,provenance}=currentReplayConfig();
 const parent='.lake/refactor-cache';mkdirSync(parent,{recursive:true});
 const directory=mkdtempSync(join(parent,'trust-replay-')),destination=join(directory,'inputs');
 const head=execFileSync('git',['rev-parse','HEAD'],{encoding:'utf8'}).trim();
 const manifest=makeReplayInputs({imports,destination,head,provenance});
 console.error(`replay-inputs: ${manifest.files.length} current objects; manifest ${join(destination,'MANIFEST.json')}`);
 console.log(resolve(destination));
}
if(process.argv[1]&&import.meta.url===pathToFileURL(process.argv[1]).href)try{main();}catch(error){console.error(error.message);process.exitCode=1;}
