'use strict';
const fs=require('node:fs');
const {join,resolve}=require('node:path');
const {createHash}=require('node:crypto');
const digest=bytes=>createHash('sha256').update(bytes).digest('hex');
const library='libSolidity_Frontend_Testing.so';
const extensions=['.olean','.olean.private','.olean.server','.ir'];
const identity=file=>{const s=fs.statSync(file,{bigint:true});return [s.dev,s.ino,s.size,s.mtimeNs,s.ctimeNs].map(String);};
function directory(root,env){return resolve(root,env.SOLIDITY_LEAN_NATIVE_DIR||'.lake/frontend-native');}

/** A native library is optional and belongs to this exact built checkout.
 * A stale or incompatible cache falls back to the normal Lean backend. */
function inspectNative(root,{env=process.env,platform=process.platform,arch=process.arch}={}){
  if(env.SOLIDITY_LEAN_NATIVE==='0')return {reason:'disabled'};
  const location=directory(root,env),manifestFile=join(location,'build.json');
  if(!fs.existsSync(manifestFile))return {reason:'not-built'};
  try{
    const manifest=JSON.parse(fs.readFileSync(manifestFile,'utf8'));
    if(manifest.schemaVersion!==1||!/^[a-f0-9]{64}$/.test(manifest.pluginSha256)||manifest.platform!==platform||manifest.architecture!==arch||
      manifest.toolchain!==fs.readFileSync(join(root,'lean-toolchain'),'utf8').trim()||
      !/^[a-f0-9]{40}$/.test(manifest.leanCommit)||!['-O0','-O1','-O2','-O3'].includes(manifest.optimization)||
      typeof manifest.nativeProbe!=='boolean')return {reason:'incompatible'};
    const setup=JSON.parse(fs.readFileSync(join(root,'.lake/build/ir/Solidity/Frontend/Testing.setup.json'),'utf8'));
    const modules=[...new Set([...Object.keys(setup.importArts).filter(n=>n.startsWith('Solidity.')),'Solidity.Frontend.Testing'])].sort();
    if(!Array.isArray(manifest.modules)||JSON.stringify(modules)!==JSON.stringify(manifest.modules.map(m=>m.module)))return {reason:'stale'};
    for(const module of manifest.modules){
      if(!/^Solidity(?:\.[A-Za-z0-9_']+)+$/.test(module.module))return {reason:'incompatible'};
      const stem=module.module.replaceAll('.','/');
      const files=[stem+'.lean','.lake/build/ir/'+stem+'.c',...extensions.map(e=>'.lake/build/lib/lean/'+stem+e).filter(p=>fs.existsSync(join(root,p)))];
      if(!module.files||JSON.stringify(files.slice().sort())!==JSON.stringify(Object.keys(module.files).sort()))return {reason:'stale'};
      if(module.sourceCSha256!==module.files['.lake/build/ir/'+stem+'.c']||(!manifest.nativeProbe&&module.cSha256!==module.sourceCSha256))return {reason:'stale'};
      for(const file of files){
        const path=join(root,file),sameIdentity=JSON.stringify(identity(path))===JSON.stringify(module.fileStats?.[file]);
        if(!sameIdentity&&digest(fs.readFileSync(path))!==module.files[file])return {reason:'stale'};
      }
    }
    if(manifest.pluginFile!==`${manifest.pluginSha256}/${library}`)return {reason:'incompatible'};
    const path=join(location,manifest.pluginFile);
    if(digest(fs.readFileSync(path))!==manifest.pluginSha256)return {reason:'stale'};
    return {path,sha256:manifest.pluginSha256,leanCommit:manifest.leanCommit,optimization:manifest.optimization,probe:manifest.nativeProbe};
  }catch{return {reason:'stale-or-unavailable'};}
}

function nativeFingerprint(root,env=process.env,{inputsOnly=false}={}){
  const location=directory(root,env),hash=createHash('sha256');
  hash.update(JSON.stringify([env.SOLIDITY_LEAN_NATIVE||'auto',location]));
  if(env.SOLIDITY_LEAN_NATIVE==='0')return hash.digest('hex');
  const stat=file=>{hash.update(file);try{hash.update(JSON.stringify(identity(file)));}catch{hash.update('missing');}};
  try{
    const raw=fs.readFileSync(join(location,'build.json'));hash.update(raw);
    const manifest=JSON.parse(raw);
    if(manifest.pluginFile===`${manifest.pluginSha256}/${library}`&&/^[a-f0-9]{64}$/.test(manifest.pluginSha256))stat(join(location,manifest.pluginFile));
    for(const module of manifest.modules||[]){
      if(!/^Solidity(?:\.[A-Za-z0-9_']+)+$/.test(module.module))continue;
      const stem=module.module.replaceAll('.','/');
      for(const file of inputsOnly?[stem+'.lean']:[stem+'.lean','.lake/build/ir/'+stem+'.c',...extensions.map(e=>'.lake/build/lib/lean/'+stem+e)])stat(join(root,file));
    }
  }catch{hash.update('missing-or-invalid-manifest');}
  if(!inputsOnly)stat(join(root,'.lake/build/ir/Solidity/Frontend/Testing.setup.json'));
  return hash.digest('hex');
}
module.exports={inspectNative,nativeFingerprint};
