// Regression: fresh replay must use Lake's selected current bytes, not stale
// physical .lake/build objects, and must fail closed on incomplete provenance.
import {test} from 'node:test';
import assert from 'node:assert/strict';
import {mkdtempSync,mkdirSync,writeFileSync,readFileSync,rmSync,existsSync,chmodSync} from 'node:fs';
import {join} from 'node:path';
import {tmpdir} from 'node:os';
import {spawnSync} from 'node:child_process';
import {makeReplayInputs,currentReplayConfig} from './trust-replay-inputs.mjs';
test('replay overlay selects current objects and rejects missing inputs',()=>{
 const root=mkdtempSync(join(tmpdir(),'trust-replay-control-'));
 try {
  const cacheDir=join(root,'cache');mkdirSync(join(cacheDir,'artifacts'),{recursive:true});
  const current=join(cacheDir,'artifacts/222.olean');writeFileSync(current,'current dependency');
  writeFileSync(join(cacheDir,'artifacts/123.olean'),'current public root');
  mkdirSync(join(root,'.lake/build/lib/lean/Solidity'),{recursive:true});
  writeFileSync(join(root,'.lake/build/lib/lean/Solidity/Dependency.olean'),'stale dependency');
  const setup={name:'Solidity.Theorems',importArts:{'Solidity.Dependency':[current]}};
  const trace={outputs:{o:['123']}},destination=join(root,'overlay');
  const manifest=makeReplayInputs({setup,trace,cacheDir,destination});
  assert.equal(readFileSync(join(destination,'Solidity/Dependency.olean'),'utf8'),'current dependency');
  assert.equal(readFileSync(join(destination,'Solidity/Theorems.olean'),'utf8'),'current public root');
  assert.equal(manifest.files.length,2);
  writeFileSync(current,'later mutation of source');
  assert.equal(readFileSync(join(destination,'Solidity/Dependency.olean'),'utf8'),'current dependency');
  assert.ok(manifest.files.every(f=>/^[a-f0-9]{64}$/u.test(f.sha256)));
  assert.throws(()=>makeReplayInputs({setup,trace,cacheDir,destination}),/already exists/);
  const missing=join(root,'missing');
  assert.throws(()=>makeReplayInputs({setup,trace:{outputs:{o:['absent']}},cacheDir,destination:missing}),/unavailable/);
  assert.equal(existsSync(missing),false);
  assert.throws(()=>makeReplayInputs({setup:{...setup,importArts:{'../escape':[current]}},trace,cacheDir,destination:join(root,'bad')}),/invalid replay module/);
 } finally {rmSync(root,{recursive:true,force:true});}
});

// Guards the cache-hit path: the persisted setup remains stale even though the
// current root trace advances; only a fresh Lake setup may select dependencies.
test('cached root cannot reuse an existing stale setup file',()=>{
 const root=mkdtempSync(join(tmpdir(),'trust-fresh-setup-'));
 try{
  const cacheDir=join(root,'cache');mkdirSync(join(cacheDir,'artifacts'),{recursive:true});
  mkdirSync(join(root,'.lake/build/lib/lean/Solidity'),{recursive:true});
  mkdirSync(join(root,'.lake/build/ir/Solidity'),{recursive:true});
  mkdirSync(join(root,'Solidity'),{recursive:true});
  writeFileSync(join(root,'Solidity/Theorems.lean'),'import Solidity.Dependency\n');
  writeFileSync(join(cacheDir,'artifacts/123.olean'),'new root');
  writeFileSync(join(cacheDir,'artifacts/222.olean'),'new dependency');
  const stale=join(root,'.lake/build/lib/lean/Solidity/Dependency.olean');writeFileSync(stale,'old dependency');
  const oldSetup={name:'Solidity.Theorems',importArts:{'Solidity.Dependency':[stale]}};
  const persisted=join(root,'.lake/build/ir/Solidity/Theorems.setup.json');writeFileSync(persisted,JSON.stringify(oldSetup));
  writeFileSync(join(root,'.lake/build/lib/lean/Solidity/Theorems.trace'),JSON.stringify({outputs:{o:['123']}}));
  const calls=[];
  const run=(cmd,args)=>{calls.push(args);if(args[0]==='build')return '';return JSON.stringify({name:'Solidity.Theorems',importArts:{'Solidity.Dependency':['cache/artifacts/222.olean']}});};
  const cfg=currentReplayConfig({root,run});
  const destination=join(root,'overlay');const manifest=makeReplayInputs({...cfg,cacheDir,destination});
  assert.deepEqual(calls,[['build','Solidity.Theorems'],['setup-file','Solidity/Theorems.lean']]);
  assert.equal(JSON.parse(readFileSync(persisted,'utf8')).importArts['Solidity.Dependency'][0],stale);
  assert.equal(readFileSync(join(destination,'Solidity/Dependency.olean'),'utf8'),'new dependency');
  assert.match(manifest.provenance.setupOrigin,/lake setup-file/);
 }finally{rmSync(root,{recursive:true,force:true});}
});

// Regression: command substitution consumes the helper's stdout as one path.
// Compiler build chatter must go to stderr even when the child writes stdout.
test('build output cannot pollute the machine-readable replay path',()=>{
 const root=mkdtempSync(join(tmpdir(),'trust-replay-stdout-'));
 try {
  mkdirSync(join(root,'Solidity'),{recursive:true});
  mkdirSync(join(root,'.lake/build/lib/lean/Solidity'),{recursive:true});
  writeFileSync(join(root,'Solidity/Theorems.lean'),'import Solidity.Dependency\n');
  writeFileSync(join(root,'.lake/build/lib/lean/Solidity/Theorems.trace'),JSON.stringify({outputs:{o:['123']}}));
  const fake=join(root,'lake');
  writeFileSync(fake,`#!${process.execPath}
if(process.argv[2]==='build'){
 process.stdout.write('compiler build noise\\n');
 process.stderr.write('compiler warning\\n');
}else console.log(JSON.stringify({name:'Solidity.Theorems',importArts:{'Solidity.Dependency':['cache/artifacts/222.olean']}}));
`);
  chmodSync(fake,0o755);
  const program=`import {execFileSync} from 'node:child_process';
import {currentReplayConfig} from ${JSON.stringify(new URL('./trust-replay-inputs.mjs',import.meta.url).href)};
currentReplayConfig({root:${JSON.stringify(root)},run:(_command,args,options)=>execFileSync(${JSON.stringify(fake)},args,options)});
console.log('RESULT');`;
  const result=spawnSync(process.execPath,['--input-type=module','-e',program],{encoding:'utf8'});
  assert.equal(result.status,0,result.stderr);
  assert.equal(result.stdout,'RESULT\n');
  assert.match(result.stderr,/compiler build noise/);
  assert.match(result.stderr,/compiler warning/);
 } finally {rmSync(root,{recursive:true,force:true});}
});
