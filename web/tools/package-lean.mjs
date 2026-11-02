import fs from 'node:fs';
import path from 'node:path';
import {fileURLToPath} from 'node:url';
import {gzipSync} from 'node:zlib';
import {createHash} from 'node:crypto';
import {execFileSync} from 'node:child_process';

// Run after building the exact pinned kernel and refreshing the native frontend
// artifacts. The latter supply portable serialized Lean environments, not native
// executable code. No host paths are embedded in the website manifest.
const root=path.resolve(path.dirname(fileURLToPath(import.meta.url)),'../..');
const [runtime,leanPrefix,output]=process.argv.slice(2);
if(!runtime||!leanPrefix||!output)throw new Error('Usage: node tools/package-lean.mjs WASM_BUILD_STAGE LEAN_4_24_PREFIX OUTPUT_DIRECTORY');
if(execFileSync(path.join(leanPrefix,'bin/lean'),['--githash'],{encoding:'utf8'}).trim()!=='797c613eb9b6d4ec95db23e3e00af9ac6657f24b')throw new Error('Native serialized libraries do not match the pinned Lean commit');
const destination=path.resolve(output);fs.mkdirSync(path.join(destination,'assets'),{recursive:true});
const previousFile=path.join(destination,'manifest.json');
const previous=fs.existsSync(previousFile)?JSON.parse(fs.readFileSync(previousFile,'utf8')):null;
const previousLibraries=new Map((previous?.libraries||[]).map(entry=>[entry.files[0].path,entry]));
fs.copyFileSync(path.join(leanPrefix,'LICENSE'),path.join(destination,'LICENSE-Lean.txt'));
fs.cpSync(path.join(leanPrefix,'LICENSES'),path.join(destination,'LICENSES'),{recursive:true});
const digest=bytes=>createHash('sha256').update(bytes).digest('hex');
const graphFile=process.env.SOLIDITY_BROWSER_IMPORT_GRAPH;
const needed=graphFile?new Set(Object.keys(JSON.parse(fs.readFileSync(graphFile,'utf8')).modules)):null;
if(needed&&['Init','Lean.Elab.Frontend','Solidity.Frontend.Testing'].some(name=>!needed.has(name)))throw new Error('Incomplete browser import graph');
if(needed?.has('Lean'))throw new Error('Browser import graph includes the umbrella Lean module; narrow its importing dependency');
function asset(bytes,extension){if(bytes.length>24*1024*1024)throw new Error('Browser asset exceeds 24 MiB');const sha256=digest(bytes),url='/lean/assets/'+sha256+'.'+extension;fs.writeFileSync(path.join(destination,'assets',sha256+'.'+extension),bytes);return {url,sha256};}
function binary(file){const bytes=fs.readFileSync(file),chunks=[];for(let offset=0;offset<bytes.length;offset+=16*1024*1024)chunks.push(asset(gzipSync(bytes.subarray(offset,offset+16*1024*1024),{level:6}),'gz'));return {chunks,size:bytes.length,sha256:digest(bytes)};}
const manifest={version:'4.24.0',commit:'797c613eb9b6d4ec95db23e3e00af9ac6657f24b',wordSize:64,gmpBits:64,
  javascript:binary(path.join(runtime,'bin/lean.js')),
  wasm:binary(path.join(runtime,'bin/lean.wasm')),libraries:[]};
const modules=new Map();
function add(module,source){if(needed&&!needed.has(module.replace(/\.(?:olean(?:\.private|\.server)?|ir)$/,'').replaceAll('/','.')))return;if(!modules.has(module))modules.set(module,new Map());modules.get(module).set('/lib/lean/'+module,source);}
const standard=path.join(leanPrefix,'lib/lean');
function visit(directory){for(const entry of fs.readdirSync(directory,{withFileTypes:true})){const file=path.join(directory,entry.name);if(entry.isDirectory())visit(file);else if(/\.(?:olean(?:\.private|\.server)?|ir)$/.test(entry.name))add(path.relative(standard,file).split(path.sep).join('/'),file);}}
for(const name of ['Init','Std','Lean']){visit(path.join(standard,name));for(const suffix of ['.olean','.olean.private','.olean.server','.ir'])if(fs.existsSync(path.join(standard,name+suffix)))add(name+suffix,path.join(standard,name+suffix));}
const setup=JSON.parse(fs.readFileSync(path.join(root,'.lake/build/ir/Solidity/Frontend/Testing.setup.json'),'utf8'));
for(const [name,artifacts]of Object.entries(setup.importArts))for(const file of artifacts){const suffix=file.match(/(\.olean(?:\.private|\.server)?|\.ir)$/)?.[1];if(suffix)add(name.replaceAll('.','/')+suffix,file);}
add('Solidity/Frontend/Testing.olean',path.join(root,'.lake/build/lib/lean/Solidity/Frontend/Testing.olean'));
// Import reads environment parts together, then reads IR in a second pass.
// Keep IR separate so the second pass cannot reinflate every environment after
// it has left the bounded cache. Preserve the original bytes and part offsets.
const groups=new Map();for(const entries of modules.values())for(const [file,source]of entries){const key=file.endsWith('.ir')?file:file.replace(/\.olean(?:\.private|\.server)?$/,'');if(!groups.has(key))groups.set(key,[]);groups.get(key).push({path:file,source});}
if(needed)for(const name of needed)if(!groups.has('/lib/lean/'+name.replaceAll('.','/')))throw new Error('Missing transitive browser library: '+name);
let rawBytes=0,compressedBytes=0;
for(const [,entries]of [...groups].sort(([a],[b])=>a.localeCompare(b))){
  let offset=0;const parts=[],files=[];
  for(const entry of entries){const bytes=fs.readFileSync(entry.source);files.push({path:entry.path,offset,size:bytes.length});offset+=bytes.length;parts.push(bytes);}
  const bytes=Buffer.concat(parts),sourceSha256=digest(bytes),old=previousLibraries.get(files[0].path);rawBytes+=offset;
  if(old?.sourceSha256===sourceSha256&&JSON.stringify(old.files)===JSON.stringify(files)&&/^\/lean\/assets\/[a-f0-9]{64}\.gz$/.test(old.url)){
    const cached=path.join(destination,old.url.slice('/lean/'.length));
    if(fs.existsSync(cached)){const compressed=fs.readFileSync(cached);if(digest(compressed)===old.sha256){compressedBytes+=compressed.length;manifest.libraries.push(old);continue;}}
  }
  const compressed=gzipSync(bytes,{level:6});compressedBytes+=compressed.length;
  manifest.libraries.push({...asset(compressed,'gz'),sourceSha256,size:offset,files});
}
manifest.build=digest(JSON.stringify(manifest));
fs.writeFileSync(path.join(destination,'manifest.json.tmp'),JSON.stringify(manifest)+'\n');fs.renameSync(path.join(destination,'manifest.json.tmp'),path.join(destination,'manifest.json'));
const referenced=new Set([...manifest.javascript.chunks,...manifest.wasm.chunks,...manifest.libraries].map(entry=>path.basename(entry.url)));
for(const name of fs.readdirSync(path.join(destination,'assets')))if(/^[a-f0-9]{64}\.gz$/.test(name)&&!referenced.has(name))fs.unlinkSync(path.join(destination,'assets',name));
const moduleCount=needed?.size??new Set([...groups.keys()].map(name=>name.replace(/\.ir$/,''))).size;
console.log(`Packaged ${moduleCount} Lean modules in ${groups.size} library assets: ${(rawBytes/1048576).toFixed(1)} MiB serialized, ${(compressedBytes/1048576).toFixed(1)} MiB compressed; build ${manifest.build}`);
