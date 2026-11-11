// Regression: replay must use current Lake selections, even when physical
// objects, persisted setups and root traces all still describe an old build.
import {test} from 'node:test';
import assert from 'node:assert/strict';
import {mkdtempSync,mkdirSync,writeFileSync,readFileSync,rmSync,existsSync,chmodSync} from 'node:fs';
import {join} from 'node:path';
import {tmpdir} from 'node:os';
import {spawnSync} from 'node:child_process';
import {makeReplayInputs,currentReplayConfig} from './trust-replay-inputs.mjs';
test('replay copies current objects including root and rejects incomplete selections',()=>{
 const root=mkdtempSync(join(tmpdir(),'trust-replay-control-'));
 try{
  const dependency=join(root,'222.olean'),publicRoot=join(root,'333.olean');
  writeFileSync(dependency,'current dependency');writeFileSync(publicRoot,'current root');
  const imports={'Solidity.Dependency':[dependency],'Solidity.Theorems':[publicRoot]},destination=join(root,'overlay');
  const m=makeReplayInputs({imports,destination});
  assert.equal(readFileSync(join(destination,'Solidity/Theorems.olean'),'utf8'),'current root');
  writeFileSync(dependency,'later mutation');
  assert.equal(readFileSync(join(destination,'Solidity/Dependency.olean'),'utf8'),'current dependency');
  assert.ok(m.files.every(f=>/^[a-f0-9]{64}$/u.test(f.sha256)));
  assert.throws(()=>makeReplayInputs({imports,destination}),/already exists/);
  assert.throws(()=>makeReplayInputs({imports:{'Solidity.Dependency':[dependency]},destination:join(root,'no-root')}),/root unavailable/);
  const missing=join(root,'missing');
  assert.throws(()=>makeReplayInputs({imports:{...imports,'Solidity.Theorems':[join(root,'absent.olean')]},destination:missing}),/unavailable/);
  assert.equal(existsSync(missing),false);
  assert.throws(()=>makeReplayInputs({imports:{...imports,'../escape':[dependency]},destination:join(root,'bad')}),/invalid replay module/);
 }finally{rmSync(root,{recursive:true,force:true});}
});
// A successful cached build need not refresh either setup or trace files.
test('stale setup and stale root trace cannot choose replay artifacts',()=>{
 const root=mkdtempSync(join(tmpdir(),'trust-fresh-graph-'));
 try{
  mkdirSync(join(root,'Solidity'),{recursive:true});mkdirSync(join(root,'.lake/build/ir/Solidity'),{recursive:true});mkdirSync(join(root,'.lake/build/lib/lean/Solidity'),{recursive:true});
  writeFileSync(join(root,'Solidity/Theorems.lean'),'import Solidity.Dependency\n');
  const stale=join(root,'.lake/build/lib/lean/Solidity/Theorems.trace');writeFileSync(stale,JSON.stringify({outputs:{o:['old']}}));
  writeFileSync(join(root,'.lake/build/ir/Solidity/Theorems.setup.json'),'stale setup');
  writeFileSync(join(root,'new-root.olean'),'new root');writeFileSync(join(root,'new-dependency.olean'),'new dependency');
  const calls=[];const run=(_cmd,args)=>{calls.push(args);if(args[0]==='build')return '';
   assert.match(readFileSync(args[2],'utf8'),/import Solidity.Theorems/);
   return JSON.stringify({name:'_unknown',importArts:{'Solidity.Theorems':['new-root.olean'],'Solidity.Dependency':['new-dependency.olean']}});};
  const cfg=currentReplayConfig({root,run}),destination=join(root,'overlay');const m=makeReplayInputs({...cfg,destination});
  assert.equal(readFileSync(join(destination,'Solidity/Theorems.olean'),'utf8'),'new root');
  assert.deepEqual(calls[0],['build','Solidity.Theorems']);assert.deepEqual(calls[1].slice(0,2),['--no-build','setup-file']);
  assert.equal(JSON.parse(readFileSync(stale,'utf8')).outputs.o[0],'old');
  assert.match(m.provenance.setupOrigin,/import Solidity.Theorems/);
 }finally{rmSync(root,{recursive:true,force:true});}
});
// Command substitution consumes exactly one path; child build noise stays stderr.
test('build output cannot pollute the machine-readable replay path',()=>{
 const root=mkdtempSync(join(tmpdir(),'trust-replay-stdout-'));
 try{
  mkdirSync(join(root,'Solidity'),{recursive:true});writeFileSync(join(root,'Solidity/Theorems.lean'),'import Solidity.Dependency\n');
  const fake=join(root,'lake');writeFileSync(fake,`#!${process.execPath}
if(process.argv[2]==='build'){
 process.stdout.write('compiler build noise\\n');process.stderr.write('compiler warning\\n');
}else console.log(JSON.stringify({name:'_unknown',importArts:{'Solidity.Theorems':['333.olean']}}));
`);chmodSync(fake,0o755);
  const program=`import {execFileSync} from 'node:child_process';
import {currentReplayConfig} from ${JSON.stringify(new URL('./trust-replay-inputs.mjs',import.meta.url).href)};
currentReplayConfig({root:${JSON.stringify(root)},run:(_command,args,options)=>execFileSync(${JSON.stringify(fake)},args,options)});
console.log('RESULT');`;
  const result=spawnSync(process.execPath,['--input-type=module','-e',program],{encoding:'utf8'});
  assert.equal(result.status,0,result.stderr);assert.equal(result.stdout,'RESULT\n');assert.match(result.stderr,/compiler build noise/);assert.match(result.stderr,/compiler warning/);
 }finally{rmSync(root,{recursive:true,force:true});}
});
