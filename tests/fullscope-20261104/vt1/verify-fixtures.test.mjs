import {mkdtempSync,cpSync,readFileSync,writeFileSync,rmSync} from 'node:fs';
import {join,dirname} from 'node:path';
import {fileURLToPath} from 'node:url';
import {tmpdir} from 'node:os';
import {createHash} from 'node:crypto';
import assert from 'node:assert/strict';
import {verify} from './verify-fixtures.mjs';
const here=dirname(fileURLToPath(import.meta.url));
assert.equal(verify().files,9);
const temp=mkdtempSync(join(tmpdir(),'vt1-provenance-'));
let count=0;
try {
  for(const mutation of ['alter-byte','swap-mode','wrong-compiler','wrong-source','rehash-swap','rehash-census','rehash-control','rehash-source-id','rehash-control-input']) {
    const dir=join(temp,mutation); cpSync(join(here,'fixtures'),dir,{recursive:true});
    const file=name=>join(dir,name);
    if(mutation==='alter-byte') writeFileSync(file('Census.unoptimized.yul'),readFileSync(file('Census.unoptimized.yul'))+' ');
    if(mutation==='swap-mode'||mutation==='rehash-swap') {
      const raw=readFileSync(file('Census.unoptimized.yul'));
      writeFileSync(file('Census.unoptimized.yul'),readFileSync(file('Census.optimized.yul')));
      writeFileSync(file('Census.optimized.yul'),raw);
    }
    if(mutation==='rehash-census') {
      const census=JSON.parse(readFileSync(file('census.json'))); census[0].functions.push('fake_helper');
      writeFileSync(file('census.json'),JSON.stringify(census));
    }
    if(mutation==='rehash-control') {
      const controls=JSON.parse(readFileSync(file('controls.json'))); controls.negative[0].diagnostics[0].message='unrelated failure';
      writeFileSync(file('controls.json'),JSON.stringify(controls));
    }
    if(mutation==='rehash-source-id') {
      const ids=JSON.parse(readFileSync(file('source-id-crosswalk.json'))); ids.crosswalk[0].definition.id+=1;
      writeFileSync(file('source-id-crosswalk.json'),JSON.stringify(ids));
    }
    if(mutation==='rehash-control-input') {
      const controls=JSON.parse(readFileSync(file('controls.json')));
      controls.negative[0].input.sources['control.yul'].content='object "A" { code { stop() } }';
      writeFileSync(file('controls.json'),JSON.stringify(controls));
    }
    if(mutation.startsWith('rehash-')) {
      const manifest=JSON.parse(readFileSync(file('manifest.json')));
      for(const entry of manifest.files) {
        const bytes=readFileSync(file(entry.name)); entry.bytes=bytes.length;
        entry.sha256=createHash('sha256').update(bytes).digest('hex');
      }
      writeFileSync(file('manifest.json'),JSON.stringify(manifest));
    }
    if(mutation==='wrong-compiler'||mutation==='wrong-source') {
      const manifest=JSON.parse(readFileSync(file('manifest.json')));
      if(mutation==='wrong-compiler') manifest.compiler.version='0.8.34';
      else manifest.sourceSha256='0'.repeat(64);
      writeFileSync(file('manifest.json'),JSON.stringify(manifest));
    }
    assert.throws(()=>verify(dir),undefined,`mutation accepted: ${mutation}`); count++;
  }
} finally { rmSync(temp,{recursive:true,force:true}); }
console.log(`PROVENANCE_CONTROLS_PASS ${count}`);
