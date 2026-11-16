#!/usr/bin/env node
// Regression boundary: cache hits can leave both physical objects and .trace
// files stale. Resolve current imports through Lake; never select by old traces.
import {readFileSync,mkdirSync,mkdtempSync,writeFileSync,rmSync,existsSync} from 'node:fs';
import {join,resolve,basename,sep} from 'node:path';
import {execFileSync} from 'node:child_process';
import {createHash} from 'node:crypto';
import {pathToFileURL} from 'node:url';
export const artifactDigest=bytes=>createHash('sha256').update(bytes).digest('hex');
export function configuredCacheDir(){
 const directory=process.env.LAKE_CACHE_DIR??execFileSync('lake',['env','printenv','LAKE_CACHE_DIR'],{encoding:'utf8'}).trim();
 if(!directory)throw Error('Lake artifact cache is disabled or unavailable');return directory;
}
export function freshArtifactGraph(module,{root=process.cwd(),run=execFileSync}={}){
 if(!/^[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*$/u.test(module))throw Error('invalid artifact root');
 const parent=join(root,'.lake/refactor-cache');mkdirSync(parent,{recursive:true});
 const directory=mkdtempSync(join(parent,'trust-artifact-query-')),file=join(directory,'Imports.lean');
 try{
  writeFileSync(file,`-- Guards against stale trace/object selection.\nimport ${module}\n`);
  const raw=run('lake',['--no-build','setup-file',file],{cwd:root,env:{...process.env,LEAN_NUM_THREADS:'1'},encoding:'utf8',stdio:['ignore','pipe','inherit'],timeout:300000,maxBuffer:64*1024*1024});
  const setup=JSON.parse(raw);if(!setup.importArts||!Array.isArray(setup.importArts[module])||!setup.importArts[module].length)throw Error('current root artifacts unavailable');
  for(const [name,paths] of Object.entries(setup.importArts)){
   if(!/^[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*$/u.test(name)||!Array.isArray(paths)||!paths.length||paths.some(p=>typeof p!=='string'))throw Error('invalid current artifact graph');
   setup.importArts[name]=paths.map(p=>resolve(root,p));
  }
  return {imports:setup.importArts,querySha256:artifactDigest(Buffer.from(raw)),origin:`lake --no-build setup-file (import ${module})`};
 }finally{rmSync(directory,{recursive:true,force:true});}
}
export function currentIleanPaths(imports,modules,{cacheDir=configuredCacheDir()}={}){
 const latest=new Map();
 for(const line of readFileSync(join(cacheDir,'inputs/solidity-lean.jsonl'),'utf8').split('\n').filter(Boolean)){
  const [key,value]=JSON.parse(line);latest.set(key,value);
 }
 const signature=xs=>[...xs].sort().join(',');const byObjects=new Map();
 for(const value of latest.values())if(value&&typeof value==='object'&&Array.isArray(value.o)&&value.o.every(h=>typeof h==='string')&&typeof value.i==='string'){
  const key=signature(value.o);if(!byObjects.has(key))byObjects.set(key,new Set());byObjects.get(key).add(value.i);
 }
 const result=new Map(),artifacts=resolve(cacheDir,'artifacts')+sep;
 for(const module of modules){
  const paths=imports[module];if(!Array.isArray(paths)||!paths.length)throw Error(`current artifact module unavailable: ${module}`);
  const objects=paths.filter(p=>/\.olean(?:\.(?:private|server))?$/u.test(p));
  if(!objects.length||objects.some(p=>!resolve(p).startsWith(artifacts)))throw Error(`cache-backed current objects required: ${module}`);
  const candidates=byObjects.get(signature(objects.map(p=>basename(p).split('.')[0])));
  if(!candidates||candidates.size!==1)throw Error(`ambiguous or missing current source index: ${module}`);
  const path=join(cacheDir,'artifacts',[...candidates][0]+'.ilean');if(!existsSync(path))throw Error(`current source index unavailable: ${module}`);result.set(module,path);
 }
 return result;
}
if(process.argv[1]&&import.meta.url===pathToFileURL(process.argv[1]).href)try{console.log(JSON.stringify(freshArtifactGraph(process.argv[2]??'Solidity.Theorems')));}catch(error){console.error(error.message);process.exitCode=1;}
