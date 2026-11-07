import {mkdtempSync,copyFileSync,readFileSync,writeFileSync,rmSync} from 'node:fs';
import {dirname,join} from 'node:path';
import {fileURLToPath} from 'node:url';
import {tmpdir} from 'node:os';
import {spawnSync} from 'node:child_process';
import assert from 'node:assert/strict';
const here=dirname(fileURLToPath(import.meta.url));
const run=dir=>spawnSync(process.execPath,[join(here,'generate-object-data.mjs'),'--check','--dir',dir],{encoding:'utf8'});
const valid=run(here); assert.equal(valid.status,0,valid.stderr);
const temp=mkdtempSync(join(tmpdir(),'vt1-object-data-'));
try {
  for(const mutation of ['source','artifact','lean-witness']) {
    for(const name of ['ObjectData.yul','object-data.json','ObjectDataChecks.lean']) copyFileSync(join(here,name),join(temp,name));
    if(mutation==='source') writeFileSync(join(temp,'ObjectData.yul'),readFileSync(join(temp,'ObjectData.yul'),'utf8')+'// altered source\n');
    if(mutation==='artifact') {
      const path=join(temp,'object-data.json'),artifact=JSON.parse(readFileSync(path));
      artifact.output.contracts['ObjectData.yul'].Root.evm.bytecode.object='00';
      writeFileSync(path,JSON.stringify(artifact,null,2)+'\n');
    }
    if(mutation==='lean-witness') {
      const path=join(temp,'ObjectDataChecks.lean');
      const offset=JSON.parse(readFileSync(join(here,'object-data.json'))).payload.offset;
      writeFileSync(path,readFileSync(path,'utf8').replace(`payload.dataoffset.val = ${offset}`,`payload.dataoffset.val = ${offset+1}`));
    }
    const rejected=run(temp); assert.notEqual(rejected.status,0,`mutation accepted: ${mutation}`);
    assert.match(rejected.stderr,/fixture differs:/);
  }
} finally { rmSync(temp,{recursive:true,force:true}); }
console.log('OBJECT_DATA_COHERENCE_PASS 3');
