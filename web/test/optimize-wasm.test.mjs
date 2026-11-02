import test from 'node:test';
import assert from 'node:assert/strict';
import {mkdtempSync,writeFileSync,readFileSync,cpSync,mkdirSync,existsSync,rmSync,readdirSync} from 'node:fs';
import {tmpdir} from 'node:os';
import path from 'node:path';
import {spawnSync} from 'node:child_process';
import {fileURLToPath} from 'node:url';

const helper=fileURLToPath(new URL('../tools/lean-wasm/optimize-wasm.sh',import.meta.url));
test('optimization cache verifies the current file after reuse, relocation and corruption',()=>{
  const root=mkdtempSync(path.join(tmpdir(),'wasm-opt-cache-'));
  try{
    const tool=path.join(root,'optimizer'),log=path.join(root,'calls');
    writeFileSync(tool,`#!/usr/bin/env python3
import os,sys,pathlib
if '--version' in sys.argv:
 print('test-only optimizer');sys.exit(0)
out=pathlib.Path(sys.argv[sys.argv.index('-o')+1])
out.write_bytes(pathlib.Path(sys.argv[1]).read_bytes()+b':optimized')
with open(os.environ['WASM_OPT_TEST_LOG'],'a') as f:f.write('called\\n')
if os.environ.get('WASM_OPT_TEST_FAIL'):sys.exit(7)
`,{mode:0o700});
    const run=(file,fail=false)=>spawnSync('bash',[helper,file,tool],{encoding:'utf8',env:{...process.env,WASM_OPT_TEST_LOG:log,...(fail?{WASM_OPT_TEST_FAIL:'1'}:{})}});
    const a=path.join(root,'a');mkdirSync(a);const input=path.join(a,'lean.wasm');writeFileSync(input,'input');
    assert.equal(run(input).status,0);assert.equal(readFileSync(input,'utf8'),'input:optimized');
    assert.equal(run(input).status,0);assert.equal(readFileSync(log,'utf8'),'called\n');
    const b=path.join(root,'b');cpSync(a,b,{recursive:true});const relocated=path.join(b,'lean.wasm');
    assert.equal(run(relocated).status,0);assert.equal(readFileSync(log,'utf8'),'called\n');
    writeFileSync(relocated,'changed');assert.equal(run(relocated).status,0);
    assert.equal(readFileSync(relocated,'utf8'),'changed:optimized');
    const failed=path.join(root,'failed.wasm');writeFileSync(failed,'preserve');
    assert.equal(run(failed,true).status,7);assert.equal(readFileSync(failed,'utf8'),'preserve');
    assert.equal(existsSync(failed+'.optimized.tmp'),false);
    assert.ok(!readdirSync(root).some(name=>name.startsWith('failed.wasm.o1-')));
  }finally{rmSync(root,{recursive:true,force:true});}
});
