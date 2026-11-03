import fs from 'node:fs';
import path from 'node:path';
import {fileURLToPath} from 'node:url';
import {createHash} from 'node:crypto';
import {execFileSync} from 'node:child_process';
import {build} from 'esbuild';

const root=path.resolve(path.dirname(fileURLToPath(import.meta.url)),'../..');
const web=path.join(root,'web'),dist=path.join(web,'dist');
const compilerName='soljson-v0.8.34+commit.80d5c536.js';
const compilerHash='c8649f8d57f81b3244c7d2dd662efc0620d1ae296f623b347a2c616a6cfd11d8';
const compilerPath=process.env.SOLIDITY_BROWSER_SOLJSON || path.join(process.env.SOLKEY_ROOT||path.join(root,'tests/migration/solkey'),'keyext.solidity.core/build/soljson',compilerName);
if(!fs.existsSync(compilerPath))throw new Error('Pinned compiler is missing. Set SOLIDITY_BROWSER_SOLJSON to the local soljson file before building.');
if(createHash('sha256').update(fs.readFileSync(compilerPath)).digest('hex')!==compilerHash)throw new Error('Compiler checksum differs from the repository pin');
const leanAssets=process.env.SOLIDITY_BROWSER_LEAN;
const preserveLean=leanAssets&&path.resolve(leanAssets)===path.join(dist,'lean');
fs.mkdirSync(dist,{recursive:true});for(const name of fs.readdirSync(dist))if(!preserveLean||name!=='lean')fs.rmSync(path.join(dist,name),{recursive:true,force:true});
for(const name of ['index.html','styles.css','app.js','manifest.json','sw.js'])fs.copyFileSync(path.join(web,name),path.join(dist,name));
// The published website always uses browser workers, including for URLs copied
// from the optional native comparison server.
const appFile=path.join(dist,'app.js');fs.writeFileSync(appFile,fs.readFileSync(appFile,'utf8').replace("const usingNativeBackend=new URLSearchParams(location.search).get('backend')==='native';",'const usingNativeBackend=false;'));
fs.copyFileSync(path.join(web,'browser/connection.js'),path.join(dist,'browser-connection.js'));
fs.copyFileSync(path.join(root,'vscode/syntaxes/solidity.tmLanguage.json'),path.join(dist,'syntax.json'));
fs.cpSync(path.join(web,'node_modules/monaco-editor/min/vs'),path.join(dist,'vendor/vs'),{recursive:true});
fs.cpSync(path.join(root,'vscode/media'),path.join(dist,'media'),{recursive:true});
fs.cpSync(path.join(web,'licenses'),path.join(dist,'licenses'),{recursive:true});
fs.copyFileSync(path.join(root,'LICENSE'),path.join(dist,'licenses/Solidity-Lean.txt'));
fs.copyFileSync(path.join(web,'THIRD_PARTY_NOTICES.md'),path.join(dist,'THIRD_PARTY_NOTICES.md'));
fs.copyFileSync(path.join(web,'node_modules/brotli-dec-wasm/pkg/brotli_dec_wasm_bg.wasm'),path.join(dist,'brotli-dec.wasm'));
for(const name of fs.readdirSync(path.join(web,'node_modules/brotli-dec-wasm')).filter(name=>name.startsWith('LICENSE-')))fs.copyFileSync(path.join(web,'node_modules/brotli-dec-wasm',name),path.join(dist,'licenses/Brotli-Decoder-'+name));
for(const [name,file]of [['Monaco','monaco-editor/LICENSE'],['Monaco-ThirdParty','monaco-editor/ThirdPartyNotices.txt'],['Noble-Hashes','@noble/hashes/LICENSE'],['Hash-Wasm','hash-wasm/LICENSE'],['Zstandard-Decoder','zstddec/LICENSE'],['Buffer','buffer/LICENSE'],['Path-Browserify','path-browserify/LICENSE'],['Fflate','fflate/LICENSE']])fs.copyFileSync(path.join(web,'node_modules',file),path.join(dist,'licenses',name+'.txt'));
fs.mkdirSync(path.join(dist,'compiler'),{recursive:true});fs.copyFileSync(compilerPath,path.join(dist,'compiler',compilerName));
if(leanAssets){if(!fs.existsSync(path.join(leanAssets,'manifest.json')))throw new Error('Lean browser manifest is missing');if(!preserveLean)fs.cpSync(leanAssets,path.join(dist,'lean'),{recursive:true});}
const directAssets=process.env.SOLIDITY_BROWSER_DIRECT;
if(directAssets){
  const manifest=JSON.parse(fs.readFileSync(path.join(directAssets,'build.json'),'utf8'));
  if(manifest.leanCommit!=='797c613eb9b6d4ec95db23e3e00af9ac6657f24b')throw new Error('Direct verifier toolchain mismatch');
  for(const name of ['direct.js','direct.wasm']){
    const bytes=fs.readFileSync(path.join(directAssets,name));
    if(createHash('sha256').update(bytes).digest('hex')!==manifest[name==='direct.js'?'javascript':'wasm'])throw new Error('Direct verifier bytes do not match its build');
  }
  for(const entry of manifest.sourceFiles){
    if(createHash('sha256').update(fs.readFileSync(path.join(root,entry.module.replaceAll('.','/')+'.lean'))).digest('hex')!==entry.sourceSha256)throw new Error('Stale direct verifier source: '+entry.module);
    const file=path.join(root,'.lake/build/ir',entry.module.replaceAll('.','/')+'.c');
    if(createHash('sha256').update(fs.readFileSync(file)).digest('hex')!==entry.cSha256)throw new Error('Stale direct verifier: '+entry.module);
  }
  fs.mkdirSync(path.join(dist,'direct'),{recursive:true});
  for(const name of ['direct.js','direct.wasm','build.json'])fs.copyFileSync(path.join(directAssets,name),path.join(dist,'direct',name));
}
const files=Object.fromEntries(fs.readdirSync(path.join(web,'examples')).filter(n=>n.endsWith('.sol')).map(n=>[n,fs.readFileSync(path.join(web,'examples',n),'utf8')]));
fs.writeFileSync(path.join(dist,'bootstrap.json'),JSON.stringify({files,backend:'browser',offline:true,protocol:1,compiler:{file:compilerName,sha256:compilerHash},lean:{version:'4.24.0',available:!!leanAssets}},null,2)+'\n');
await build({entryPoints:[path.join(web,'browser/worker.mjs')],outfile:path.join(dist,'browser-worker.js'),bundle:true,format:'iife',platform:'browser',target:'es2022',minify:false,
  inject:[path.join(web,'browser/globals.mjs')],define:{'import.meta.url':'"file:///runtime/scripts/solc-ast.mjs"'},
  plugins:[{name:'browser-memory-platform',setup(b){b.onResolve({filter:/^node:/},()=>({path:path.join(web,'browser/platform.mjs')}));}}]
});
await build({entryPoints:[path.join(web,'browser/direct-worker.js')],outfile:path.join(dist,'direct-worker.js'),bundle:true,format:'iife',platform:'browser',target:'es2022',minify:true});
await build({entryPoints:[path.join(web,'browser/kernel-worker.js')],outfile:path.join(dist,'kernel-worker.js'),bundle:true,format:'iife',platform:'browser',target:'es2022',minify:true});
const csp="default-src 'self'; script-src 'self' 'unsafe-eval'; worker-src 'self' blob:; style-src 'self' 'unsafe-inline'; img-src 'self' data:; font-src 'self' data:; connect-src 'self' data:; object-src 'none'; base-uri 'none'";
fs.writeFileSync(path.join(dist,'_headers'),`/*\n  Content-Security-Policy: ${csp}\n  X-Content-Type-Options: nosniff\n  Referrer-Policy: no-referrer\n  Cross-Origin-Opener-Policy: same-origin\n  Cross-Origin-Embedder-Policy: require-corp\n`);
const assets=[];function visit(directory){for(const entry of fs.readdirSync(directory,{withFileTypes:true})){const file=path.join(directory,entry.name);if(entry.isDirectory())visit(file);else if(!['_headers','asset-manifest.json'].includes(entry.name))assets.push('/'+path.relative(dist,file).split(path.sep).join('/'));}}visit(dist);
const revision=createHash('sha256');for(const asset of [...assets].sort())revision.update(asset).update(fs.readFileSync(path.join(dist,asset.slice(1))));const buildId=revision.digest('hex');
const serviceWorker=path.join(dist,'sw.js');fs.writeFileSync(serviceWorker,fs.readFileSync(serviceWorker,'utf8').replace('const REQUIRE_ASSET_MANIFEST = false;','const REQUIRE_ASSET_MANIFEST = true;').replace('solidity-lean-browser-workbench-v4','solidity-lean-browser-workbench-'+buildId.slice(0,16)));
fs.writeFileSync(path.join(dist,'asset-manifest.json'),JSON.stringify({version:1,build:buildId,assets},null,2)+'\n');
console.log(`Static website built: ${dist}\n${assets.length} same-origin assets; Solidity compiler checksum verified. No backend is included.`);
