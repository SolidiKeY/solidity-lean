#!/usr/bin/env node
// Exercise the real gate and Git ranges in an isolated fixture; no Lean is run.
import assert from 'node:assert/strict';
import {execFileSync,spawnSync} from 'node:child_process';
import {chmodSync,copyFileSync,mkdirSync,mkdtempSync,readFileSync,rmSync,writeFileSync} from 'node:fs';
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
 // Advance the integration base with reserved source/frontend/trust work and
 // registry additions. None of it may be dropped by the lane's contribution.
 const originalBoundary=git(['rev-parse','HEAD']);
 const reserved=[
  'Solidity/Source/Session.lean','Solidity/Source/ExprProgress.lean',
  'Solidity/Frontend/Static/InferExamples.lean','TrustAudit.lean','scripts/g07-axiom-pins.json'];
 for(const file of reserved)write(file,'-- retained source integration\n');
 for(const file of ['Solidity.lean','docs/README.md','docs/module-map.md'])
  write(file,'-- retained registry entry\n-- advanced base registry entry\n');
 git(['add','.']);commit();
 // Give the isolated history its advanced integration boundary; keep real
 // dependency/source/scalar/storage pins. Exercise the default, with no flags.
 const boundary=git(['rev-parse','HEAD']);
 const gateFile=join(fixture,'scripts/check-backend-environment.mjs');
 const gateSource=readFileSync(gateFile,'utf8');
 assert.ok(gateSource.includes("const integrationBase='b965d675e260a374401b131e59d501f8ce5da147';"));
 write('scripts/check-backend-environment.mjs',gateSource.replace(
  "const integrationBase='b965d675e260a374401b131e59d501f8ce5da147';",
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
 write('docs/README.md','-- retained registry entry\n-- advanced base registry entry\n');gate(/shared registry is not append-only/);
 git(['reset','-q','HEAD','--','docs/README.md']);
 write('docs/README.md','-- retained registry entry\n-- advanced base registry entry\n-- appended entry\n');gate(null);
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
 write('docs/README.md','-- retained registry entry\n-- advanced base registry entry\n-- committed append\n');
 git(['add','docs/README.md']);commit();cleanGate(null);
 git(['reset','--hard',before]);
 // Dropping only the advanced base's rows (while retaining the older base)
 // must fail both committed and live/index checks for every shared registry.
 for(const file of ['Solidity.lean','docs/README.md','docs/module-map.md']){
  write(file,git(['show',`${originalBoundary}:${file}`])+'\n');
  gate(/shared registry is not append-only/);
  git(['add',file]);commit();cleanGate(/shared registry is not append-only/);
  git(['reset','--hard',before]);
 }
 for(const file of reserved){
  git(['rm',file]);commit();cleanGate(/unowned write/);
  git(['reset','--hard',before]);
 }
 // A committed change to a pinned other-lane file cannot use the exemption.
 write('Solidity/Backend/Scalar/Slice.lean','-- changed scalar contribution\n');
 git(['add','.']);commit();cleanGate(/integrated scalar file changed/);
 git(['reset','--hard',before]);
 // The concurrent storage integration is accepted only at its exact snapshot,
 // including file mode; modifying it is not an ownership exemption.
 const storageFile='Solidity/Storage/Representation/Model.lean';
 const storageHead='8db4c673cd2d0c434221cbf5d398e1a92cf7ea4f';
 write(storageFile,execFileSync('git',['show',`${storageHead}:${storageFile}`],{cwd:fixture,encoding:'utf8'}));
 git(['add',storageFile]);commit();cleanGate(null);
 const withStorage=git(['rev-parse','HEAD']);
 write(storageFile,'-- modified integrated storage\n');
 gate(/integrated storage file changed/);
 git(['add',storageFile]);commit();cleanGate(/integrated storage file changed/);
 git(['reset','--hard',withStorage]);
 chmodSync(join(fixture,storageFile),0o755);git(['add',storageFile]);commit();
 cleanGate(/integrated storage file changed/);
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
 rmSync(join(fixture,'Solidity/Frontend/Fixture.lean'));
 git(['restore','Solidity/Backend/Environment/Fixture0.lean']);
 write('Solidity/Backend/Environment/Fixture0.lean','axiom unsound : False\n');
 gate(/proof shortcut\/budget/);
 console.log('ownership regressions pass: advanced integration base and reserved source/trust preservation, contribution range, live repairs, unowned writes/renames, registry deletion, default committed violations/appends, pinned scalar/storage blobs and modes, explicit range, frozen imports, closure, proof gate');
}finally{rmSync(fixture,{recursive:true,force:true});}
