import test from 'node:test';
import assert from 'node:assert/strict';
import {mkdtempSync,mkdirSync,readFileSync,writeFileSync,rmSync,readdirSync} from 'node:fs';
import {tmpdir} from 'node:os';
import {join,resolve,dirname} from 'node:path';
import {fileURLToPath} from 'node:url';
import {execFileSync} from 'node:child_process';
import {runTool} from './test-solidity.mjs';

// Explicit serial integration target; caller holds the repository writer lock.
// All destructive cache controls are confined to this owned temporary worktree.
test('ordinary native build ignores absent and stale local C after artifact-cache reuse',()=>{
  const root=resolve(dirname(fileURLToPath(import.meta.url)),'..');
  const solkey=resolve(root,process.env.SOLKEY_ROOT??'../solkey');
  const parent=mkdtempSync(join(tmpdir(),'verify-cache-control-')),tree=join(parent,'tree');
  let added=false;
  try {
    execFileSync('git',['worktree','add','--detach',tree,'HEAD'],{stdio:'pipe'});added=true;
    runTool('lake',['-d',tree,'build','Solidity.Tools.FastMode.Engine'],600000);
    const local=join(tree,'.lake/build/ir/Solidity');
    rmSync(local,{recursive:true,force:true});
    const stale=join(local,'Tools/FastMode/Engine.c'),sentinel='#error stale local C must never be consumed\n';
    mkdirSync(resolve(stale,'..'),{recursive:true});writeFileSync(stale,sentinel);
    const report=JSON.parse(runTool(process.execPath,[join(tree,'scripts/verify.mjs'),
      join(tree,'scripts/verify-fixtures/InvariantLeaves.sol'),'--mode','fast','--compare','--json',
      '--contract','TestSuite','--function','whileCountsUp','--solkey',solkey],600000));
    assert.equal(report.status,'agree');assert.equal(report.fast.results[0].verification,'native');
    assert.equal(readFileSync(stale,'utf8'),sentinel);
    const native=join(tree,'.lake/verify/native');
    const builds=readdirSync(native).map(key=>JSON.parse(readFileSync(join(native,key,'build.json'),'utf8')));
    assert.equal(builds.length,1);
    const engine=builds[0].sourceFiles.find(row=>row.module==='Solidity.Tools.FastMode.Engine');
    assert.ok(engine);assert.notEqual(engine.cPath,stale);
    assert.equal(builds[0].selectedArtifacts[engine.cPath],engine.cSha256);
  } finally {
    if(added)execFileSync('git',['worktree','remove','--force',tree],{stdio:'pipe'});
    rmSync(parent,{recursive:true,force:true});
  }
});
