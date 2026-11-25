import test from 'node:test';
import assert from 'node:assert/strict';
import {mkdtempSync, writeFileSync, readFileSync, rmSync} from 'node:fs';
import {tmpdir} from 'node:os';
import {join, resolve} from 'node:path';
import {spawnSync} from 'node:child_process';
const script=resolve('scripts/ci/build-observation-prerequisites.sh');
function run(body, config='name = "test"\n[[lean_lib]]\nname = "Solidity"\nweakLeanArgs = ["-j1", "--tstack=131072"]\n') {
  const dir=mkdtempSync(join(tmpdir(),'observation-prerequisites-'));
  try {
    const log=join(dir,'log'), cfg=join(dir,'lake.toml');
    writeFileSync(cfg,config);
    writeFileSync(join(dir,'timeout'),'#!/bin/bash\necho "timeout:$1" >> "$LOG"\nshift\nexec "$@"\n',{mode:0o700});
    writeFileSync(join(dir,'lake'),'#!/bin/bash\necho "lake:$LEAN_NUM_THREADS:$*" >> "$LOG"\n'+body+'\n',{mode:0o700});
    const result=spawnSync('bash',[script,cfg],{env:{...process.env,PATH:dir+':'+process.env.PATH,LOG:log},encoding:'utf8'});
    let lines=[];try {lines=readFileSync(log,'utf8').trim().split('\n');} catch {}
    return {result,lines};
  } finally {rmSync(dir,{recursive:true,force:true});}
}
test('one deadline encloses ordered serial targets',()=>{
  const {result,lines}=run('exit 0'); assert.equal(result.status,0);
  assert.equal(lines[0],'timeout:300'); assert.equal(lines.length,4);
  for (const [i,name] of ['Paths','Values','Ops'].entries()) {
    assert.match(lines[i+1],new RegExp('^lake:1:--file .* build Solidity\\.Theory\\.Typed\\.Obs\\.'+name+':leanArts$'));
  }
});
test('failed module stops the group before later targets',()=>{
  const {result,lines}=run('[[ "$*" != *Obs.Values:leanArts* ]] || exit 7');
  assert.equal(result.status,7);assert.equal(lines.length,3);
  assert.ok(!lines.some(line=>line.includes('Obs.Ops:leanArts')));
});
test('nonserial configuration is refused before launching Lake',()=>{
  const {result,lines}=run('exit 0','[[lean_lib]]\nname="Solidity"\nweakLeanArgs=["--tstack=131072"]\n');
  assert.notEqual(result.status,0);assert.deepEqual(lines,[]);
});
test('missing configuration argument is refused',()=>{
  assert.equal(spawnSync('bash',[script]).status,2);
});

test('required flags do not admit later conflicting overrides',()=>{
  for (const extra of ['-j8','--threads=8','--tstack=262144']) {
    const {result,lines}=run('exit 0','[[lean_lib]]\nname="Solidity"\nweakLeanArgs=["-j1","--tstack=131072","'+extra+'"]\n');
    assert.notEqual(result.status,0);assert.deepEqual(lines,[]);
  }
});
test('strong library and package Lean arguments are refused',()=>{
  for (const config of [
    '[[lean_lib]]\nname="Solidity"\nweakLeanArgs=["-j1","--tstack=131072"]\nleanArgs=["-j8"]\n',
    'moreLeanArgs=["-j8"]\n[[lean_lib]]\nname="Solidity"\nweakLeanArgs=["-j1","--tstack=131072"]\n'
  ]) {
    const {result,lines}=run('exit 0',config);
    assert.notEqual(result.status,0);assert.deepEqual(lines,[]);
  }
});
