#!/usr/bin/env node
// Exercise the real gate and Git ranges in an isolated fixture; no Lean is run.
import assert from 'node:assert/strict';
import {execFileSync,spawnSync} from 'node:child_process';
import {copyFileSync,mkdirSync,mkdtempSync,readFileSync,rmSync,writeFileSync} from 'node:fs';
import {tmpdir} from 'node:os';
import {dirname,join,resolve} from 'node:path';
import {fileURLToPath} from 'node:url';

const root=fileURLToPath(new URL('../..',import.meta.url));
const fixture=mkdtempSync(join(tmpdir(),'environment-ownership-'));
const objects=execFileSync('git',['rev-parse','--git-path','objects'],{cwd:root,encoding:'utf8'}).trim();
const git=args=>execFileSync('git',args,{cwd:fixture,encoding:'utf8',stdio:['ignore','pipe','pipe']}).trim();
const write=(file,text)=>{mkdirSync(dirname(join(fixture,file)),{recursive:true});writeFileSync(join(fixture,file),text);};
const commit=()=>git(['-c','user.name=Fixture','-c','user.email=fixture@example.invalid','commit','-qm','Fixture']);
function gate(expected,...args){
 const result=spawnSync(process.execPath,['scripts/check-backend-environment.mjs',...args],{cwd:fixture,encoding:'utf8'});
 assert.ifError(result.error);
 if(expected===null)assert.equal(result.status,0,result.stderr);
 else{assert.notEqual(result.status,0);assert.match(result.stderr,expected);}
}
function cleanGate(expected){
 assert.equal(git(['status','--porcelain']),'','committed regression fixture must be clean');
 gate(expected);
}
try{
 git(['init','-q']);
 // Reuse only read-only objects, including the pinned contribution/dependency base.
 write('.git/objects/info/alternates',resolve(root,objects)+'\n');
 for(const file of ['scripts/check-backend-environment.mjs','scripts/import-fanout.mjs']){
  mkdirSync(dirname(join(fixture,file)),{recursive:true});copyFileSync(join(root,file),join(fixture,file));
 }
 for(let i=0;i<11;i++)write(`Solidity/Backend/Environment/Fixture${i}.lean`,'-- fixture\n');
 for(const file of ['Solidity.lean','docs/README.md','docs/module-map.md'])write(file,'-- retained registry entry\n');
 write('outside.txt','retained\n');
 git(['add','.']);commit();
 // Give this isolated history its own integration boundary; keep real frozen
 // dependency/source/scalar pins. Exercise the normal invocation, with no flags.
 const boundary=git(['rev-parse','HEAD']);
 const gateFile=join(fixture,'scripts/check-backend-environment.mjs');
 const gateSource=readFileSync(gateFile,'utf8');
 assert.ok(gateSource.includes("const integrationBase='8445c3fc203144251b9d1fc9181f7f61a8189522';"));
 write('scripts/check-backend-environment.mjs',gateSource.replace(
  "const integrationBase='8445c3fc203144251b9d1fc9181f7f61a8189522';",
  `const integrationBase='${boundary}';`));
 git(['add','.']);commit();
 gate(null);
 write('tests/backend-environment/owned.txt','allowed repair\n');gate(null);
 write('unowned.txt','unowned repair\n');gate(/unowned write unowned.txt/);
 rmSync(join(fixture,'unowned.txt'));
 write('outside.txt','changed\n');gate(/unowned write outside.txt/);
 git(['restore','outside.txt']);
 write('outside.txt','staged violation\n');git(['add','outside.txt']);
 write('outside.txt','retained\n');gate(/unowned write outside.txt/);
 git(['reset','-q','HEAD','--','outside.txt']);
 write('docs/README.md','');gate(/shared registry is not append-only/);
 git(['restore','docs/README.md']);
 write('docs/README.md','');git(['add','docs/README.md']);
 write('docs/README.md','-- retained registry entry\n');gate(/shared registry is not append-only/);
 git(['reset','-q','HEAD','--','docs/README.md']);
 write('docs/README.md','-- retained registry entry\n-- appended entry\n');gate(null);
 git(['restore','docs/README.md']);
 rmSync(join(fixture,'tests/backend-environment/owned.txt'));
 // Clean committed violations must fail under the normal gate invocation.
 const before=git(['rev-parse','HEAD']);
 write('outside.txt','committed violation\n');git(['add','outside.txt']);commit();
 const after=git(['rev-parse','HEAD']);
 cleanGate(/unowned write outside.txt/);
 gate(/unowned write outside.txt/,'--ownership-base',before,'--ownership-head',after);
 git(['reset','--hard',before]);
 for(const file of ['Solidity.lean','docs/README.md','docs/module-map.md']){
  write(file,'');git(['add',file]);commit();
  cleanGate(/shared registry is not append-only/);
  git(['reset','--hard',before]);
 }
 write('docs/README.md','-- retained registry entry\n-- committed append\n');
 git(['add','docs/README.md']);commit();cleanGate(null);
 git(['reset','--hard',before]);
 // A committed change to a pinned other-lane file cannot use the exemption.
 write('Solidity/Backend/Scalar/Slice.lean','-- changed scalar contribution\n');
 git(['add','.']);commit();cleanGate(/integrated scalar file changed/);
 git(['reset','--hard',before]);
 gate(/supply both/,'--ownership-base',before);
 // Re-selecting the ownership range must never refresh the dependency base.
 write('Solidity/Backend/EnvironmentMissingDependency.lean','-- new other-lane dependency\n');
 git(['add','Solidity/Backend/EnvironmentMissingDependency.lean']);commit();
 const newerBase=git(['rev-parse','HEAD']);
 write('Solidity/Backend/Environment/Fixture0.lean','import Solidity.Backend.EnvironmentMissingDependency\n');
 gate(/imports unavailable\/new other lane/,'--ownership-base',newerBase,'--ownership-head',newerBase);
 git(['reset','--hard',before]);
 // Renaming an unowned file into the lane must still expose its unowned deletion.
 git(['mv','outside.txt','Solidity/Backend/Environment/Moved.lean']);
 gate(/unowned write outside.txt/);git(['reset','--hard',before]);
 write('Solidity/Frontend/Fixture.lean','-- forbidden closure\n');
 write('Solidity/Backend/Environment/Fixture0.lean','import Solidity.Frontend.Fixture\n');
 gate(/reaches frontend\/external lane/);
 rmSync(join(fixture,'Solidity/Frontend'),{recursive:true});
 git(['restore','Solidity/Backend/Environment/Fixture0.lean']);
 write('Solidity/Backend/Environment/Fixture0.lean','axiom unsound : False\n');
 gate(/proof shortcut\/budget/);
 console.log('ownership regressions pass: contribution range, live repairs, unowned writes/renames, registry deletion, default committed violations/appends, pinned scalar files, explicit range, frozen imports, closure, proof gate');
}finally{rmSync(fixture,{recursive:true,force:true});}
