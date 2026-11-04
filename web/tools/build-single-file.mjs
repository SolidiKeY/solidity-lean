import fs from 'node:fs';
import path from 'node:path';
import {fileURLToPath} from 'node:url';
import {createHash} from 'node:crypto';
import {gunzipSync,zstdCompressSync,zstdDecompressSync,constants} from 'node:zlib';
import {build} from 'esbuild';

// The existing static build supplies byte-for-byte pinned runtime inputs.
// General proof-authoring assets are an explicit opt-in. Ordinary IDE checks
// use only the compiled verifier, with no serialized Lean environment.
const web=path.resolve(path.dirname(fileURLToPath(import.meta.url)),'..');
const dist=path.join(web,'dist'),output=path.join(web,'single-file'),temporary=path.join(web,'.single-file-assets');
const withLegacy=process.argv.includes('--with-legacy');
const manifest=withLegacy?JSON.parse(fs.readFileSync(path.join(dist,'lean/manifest.json'),'utf8')):null;
if(!fs.existsSync(path.join(dist,'direct/build.json')))throw new Error('The compiled verifier must be built before packaging the IDE');
fs.mkdirSync(temporary,{recursive:true});
fs.mkdirSync(output,{recursive:true});
const assets=new Map(),hash=bytes=>createHash('sha256').update(bytes).digest('hex');
const add=(url,file,type='application/octet-stream')=>assets.set(url,{file,type});
const text=(url,contents,type)=>{const file=path.join(temporary,hash(Buffer.from(url)));fs.writeFileSync(file,contents);add(url,file,type);};
const repacked=new Map();
for(const chunk of manifest?[...manifest.javascript.chunks,...manifest.wasm.chunks,...manifest.libraries]:[]){
  if(repacked.has(chunk.url)){Object.assign(chunk,repacked.get(chunk.url));continue;}
  const original=fs.readFileSync(path.join(dist,chunk.url.slice(1)));
  if(hash(original)!==chunk.sha256)throw new Error('Corrupt input asset: '+chunk.url);
  const file=path.join(temporary,chunk.sha256+'.zstd-15');
  const raw=gunzipSync(original);
  const compressed=fs.existsSync(file)?fs.readFileSync(file):zstdCompressSync(raw,{params:{[constants.ZSTD_c_compressionLevel]:15}});
  if(hash(zstdDecompressSync(compressed))!==hash(raw))throw new Error('Corrupt Zstandard cache: '+file);
  if(!fs.existsSync(file))fs.writeFileSync(file,compressed);
  const sha256=hash(compressed),url='/lean/assets/'+sha256+'.zst';
  add(url,file);repacked.set(chunk.url,{url,sha256,size:raw.length});Object.assign(chunk,{url,sha256,size:raw.length});
}
if(manifest){
  manifest.compression='zstd';delete manifest.build;manifest.build=hash(JSON.stringify(manifest));
  text('/lean/manifest.json',JSON.stringify(manifest),'application/json');
}
await build({entryPoints:[path.join(web,'node_modules/monaco-editor/esm/vs/editor/edcore.main.js')],outfile:path.join(temporary,'monaco.js'),bundle:true,format:'iife',globalName:'monaco',target:'es2022',minify:true,loader:{'.ttf':'dataurl'},legalComments:'inline'});
await build({entryPoints:[path.join(web,'node_modules/monaco-editor/esm/vs/editor/editor.worker.js')],outfile:path.join(temporary,'monaco-worker.js'),bundle:true,format:'iife',target:'es2022',minify:true});
for(const name of ['monaco.js','monaco-worker.js','monaco.css'])add('/'+name,path.join(temporary,name),name.endsWith('.css')?'text/css':'text/javascript');
for(const name of ['bootstrap.json','syntax.json','browser-connection.js','browser-worker.js','direct-worker.js','app.js',...(withLegacy?['kernel-worker.js','brotli-dec.wasm']:[])])add('/'+name,path.join(dist,name),name.endsWith('.json')?'application/json':name.endsWith('.wasm')?'application/wasm':'text/javascript');
if(fs.existsSync(path.join(dist,'direct/build.json')))for(const name of ['direct.js','direct.wasm','build.json'])add('/direct/'+name,path.join(dist,'direct',name),name.endsWith('.wasm')?'application/wasm':name.endsWith('.json')?'application/json':'text/javascript');
add('/compiler/soljson-v0.8.34+commit.80d5c536.js',path.join(dist,'compiler/soljson-v0.8.34+commit.80d5c536.js'),'text/javascript');
for(const name of fs.readdirSync(path.join(dist,'media')))add('/media/'+name,path.join(dist,'media',name),'image/svg+xml');
const svg=name=>'data:image/svg+xml;base64,'+fs.readFileSync(path.join(dist,'media',name)).toString('base64');
const css=fs.readFileSync(path.join(dist,'styles.css'),'utf8').replace(/url\(['"]?\/media\/([^'"\)]+)['"]?\)/g,(_,name)=>`url('${svg(name)}')`);
text('/styles.css',css,'text/css');
// Preserve all license notices in the downloadable HTML itself.
const notices=[];
function licenses(dir){for(const entry of fs.readdirSync(dir,{withFileTypes:true})){const file=path.join(dir,entry.name);if(entry.isDirectory())licenses(file);else notices.push(path.relative(dist,file)+'\n'+fs.readFileSync(file,'utf8'));}}
licenses(path.join(dist,'licenses'));
for(const name of ['LICENSES','LICENSE-Lean.txt'])if(fs.existsSync(path.join(dist,'lean',name)))notices.push(fs.readFileSync(path.join(dist,'lean',name),'utf8'));
notices.push(fs.readFileSync(path.join(dist,'THIRD_PARTY_NOTICES.md'),'utf8'));
text('/THIRD_PARTY_NOTICES.txt',notices.join('\n\n'),'text/plain');
const revision=createHash('sha256');for(const [url,{file}]of assets)revision.update(url).update(fs.readFileSync(file));revision.update(fs.readFileSync(path.join(web,'browser/single-file.js'))).update(fs.readFileSync(path.join(dist,'index.html')));const buildId=revision.digest('hex');
let html=fs.readFileSync(path.join(dist,'index.html'),'utf8').replace(/  <(?:link|script)[^\n]*\n/g,'');
const csp="default-src 'none'; script-src 'unsafe-inline' 'unsafe-eval' blob:; worker-src blob:; connect-src blob: data:; style-src 'unsafe-inline' blob:; img-src blob: data:; font-src blob: data:; base-uri 'none'; object-src 'none'";
html=html.replace('<meta charset="utf-8">',`<meta charset="utf-8">\n  <meta http-equiv="Content-Security-Policy" content="${csp}">\n  <link rel="icon" href="${svg('proved.svg')}">`);
html=html.replace('</head>',`<style>${css}</style></head>`).replace('</body>\n</html>','');
const destination=path.join(output,'index.html'),fd=fs.openSync(destination+'.tmp','w');
fs.writeSync(fd,html+'\n<script>\n'+fs.readFileSync(path.join(web,'browser/single-file.js'),'utf8')+`\nprepareSingleFile(${JSON.stringify(buildId)},${assets.size});\n</script>\n`);
let compressedBytes=0;
for(const [url,{file,type}]of assets){
  const bytes=fs.readFileSync(file);compressedBytes+=bytes.length;
  fs.writeSync(fd,`<script type="application/octet-stream" data-asset="${url}" data-mime="${type}">${bytes.toString('base64')}</script><script>singleFileIDE.capture();</script>\n`);
}
fs.writeSync(fd,'<script>singleFileIDE.finish().catch(singleFileIDE.fail);</script>\n</body></html>\n');fs.closeSync(fd);
const size=fs.statSync(destination+'.tmp').size;
if(size>990_000_000)throw new Error('Single HTML exceeds the deployment budget (990 MB)');
fs.renameSync(destination+'.tmp',destination);
const direct=JSON.parse(fs.readFileSync(path.join(dist,'direct/build.json'),'utf8'));
const report={build:buildId,kernelBuild:manifest?.build??null,assets:assets.size,assetBytes:compressedBytes,htmlBytes:size,compression:manifest?'zstd':null,runtimeSha256:direct.wasm,compiledOnly:!withLegacy};
fs.writeFileSync(path.join(output,'build.json'),JSON.stringify(report,null,2)+'\n');
console.log(JSON.stringify(report,null,2));
