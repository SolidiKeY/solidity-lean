'use strict';
const {test}=require('node:test');
const assert=require('node:assert/strict');
const fs=require('node:fs');
const {spawnSync}=require('node:child_process');
const {join,dirname,resolve}=require('node:path');
const {tmpdir}=require('node:os');
const {inspectNative}=require('../src/native-plugin.cjs');
const available=process.platform!=='win32'&&spawnSync('python3',['--version']).status===0;

test('native builder publishes immutable inputs atomically and rejects concurrent frontend changes',{skip:!available},()=>{
 const root=fs.mkdtempSync(join(tmpdir(),'native-builder-')),prefix=join(root,'tools'),output=join(root,'.lake/frontend-native');
 const put=(file,bytes)=>{fs.mkdirSync(dirname(join(root,file)),{recursive:true});fs.writeFileSync(join(root,file),bytes);};
 const stem='Solidity/Frontend/Testing';
 put('lean-toolchain','leanprover/lean4:v4.24.0\n');put(stem+'.lean','source');
 put('.lake/build/ir/'+stem+'.setup.json',JSON.stringify({importArts:{}}));put('.lake/build/ir/'+stem+'.c','captured C v1');
 for(const ext of ['.olean','.olean.private','.olean.server','.ir'])put('.lake/build/lib/lean/'+stem+ext,'artifact '+ext);
 put('mode','normal');
 const python=spawnSync('python3',['-c','import sys; print(sys.executable)'],{encoding:'utf8'}).stdout.trim();
 put('tools/bin/lean',`#!${python}\nprint('${'1'.repeat(40)}')\n`);
 put('tools/bin/leanc',`#!${python}
from pathlib import Path
import sys
root=Path(${JSON.stringify(root)})
mode=(root/'mode').read_text()
out=Path(sys.argv[sys.argv.index('-o')+1])
if '-c' in sys.argv:
    captured=Path(sys.argv[sys.argv.index('-c')+1]).read_bytes()
    (root/'compiled-input').write_bytes(captured)
    out.write_bytes(b'object')
    if mode=='during-compile': (root/'.lake/build/ir/${stem}.c').write_text('concurrent C')
else:
    out.write_bytes(b'linked native fixture')
    if mode=='during-link': (root/'.lake/build/lib/lean/${stem}.olean.private').write_text('concurrent private artifact')
`);
 fs.chmodSync(join(prefix,'bin/lean'),0o755);fs.chmodSync(join(prefix,'bin/leanc'),0o755);
 const run=()=>spawnSync('python3',[resolve(__dirname,'../../scripts/build-frontend-plugin.py'),prefix,output],{cwd:root,env:{...process.env,BENCH_NATIVE_PROBE:'0',BENCH_C_OPT:'-O0'},encoding:'utf8'});
 try{
  const first=run();assert.equal(first.status,0,first.stderr);
  const manifest=fs.readFileSync(join(output,'build.json'));const metadata=JSON.parse(manifest);
  assert.equal(metadata.pluginFile,metadata.pluginSha256+'/libSolidity_Frontend_Testing.so');assert.ok(inspectNative(root,{env:{}}).path);
  const previous=fs.readFileSync(join(output,'libSolidity_Frontend_Testing.so'));
  put('mode','during-compile');put('.lake/build/ir/'+stem+'.c','captured C v2');
  const racing=run();assert.notEqual(racing.status,0);assert.match(racing.stderr,/C input changed/);
  assert.equal(fs.readFileSync(join(root,'compiled-input'),'utf8'),'captured C v2');
  assert.deepEqual(fs.readFileSync(join(output,'build.json')),manifest);assert.deepEqual(fs.readFileSync(join(output,'libSolidity_Frontend_Testing.so')),previous);
  put('mode','during-link');put('.lake/build/ir/'+stem+'.c','captured C v3');
  const late=run();assert.notEqual(late.status,0);assert.match(late.stderr,/Frontend changed during native build/);
  assert.deepEqual(fs.readFileSync(join(output,'build.json')),manifest);assert.deepEqual(fs.readFileSync(join(output,'libSolidity_Frontend_Testing.so')),previous);
  assert.equal(inspectNative(root,{env:{}}).reason,'stale');
 }finally{fs.rmSync(root,{recursive:true,force:true});}
});
