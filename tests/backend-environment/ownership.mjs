#!/usr/bin/env node
// Exercise the real gate and Git ranges in an isolated fixture; no Lean is run.
import assert from 'node:assert/strict';
import {execFileSync,spawnSync} from 'node:child_process';
import {chmodSync,copyFileSync,mkdirSync,mkdtempSync,readFileSync,rmSync,symlinkSync,writeFileSync} from 'node:fs';
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
 write('lakefile.toml','[[lean_lib]]\nname = "Fixture"\nweakLeanArgs = ["--tstack=131072"]\n');
 git(['add','.']);commit();
 // Advance the integration base with reserved source/frontend/trust work and
 // registry additions. None of it may be dropped by the lane's contribution.
 const originalBoundary=git(['rev-parse','HEAD']);
 const reserved=[
  'Solidity/Source/Session.lean','Solidity/Source/ExprProgress.lean',
  'Solidity/Frontend/Static/InferExamples.lean','TrustAudit.lean','scripts/g07-axiom-pins.json',
  'Solidity/Source/SoundnessExamples.lean','Solidity/Source/WellTyped.lean',
  'docs/feature-work/source-soundness.md'];
 for(const file of reserved)write(file,'-- retained source integration\n');
 for(const file of ['Solidity.lean','docs/README.md','docs/module-map.md'])
  write(file,'-- retained registry entry\n-- advanced base registry entry\n');
 git(['add','.']);commit();
 // Give the isolated history its advanced integration boundary; keep real
 // dependency/source/scalar/storage pins. Exercise the default, with no flags.
 const boundary=git(['rev-parse','HEAD']);
 // An earlier refreshed base is superseded by further authorized source work.
 for(const file of reserved)write(file,'-- earlier refreshed source integration\n');
 for(const file of ['Solidity.lean','docs/README.md','docs/module-map.md'])
  write(file,'-- retained registry entry\n-- refreshed base registry entry\n');
 git(['add','.']);commit();
 const previousRefresh=git(['rev-parse','HEAD']);
 // A previously repaired pin can itself become stale after the final merge.
 // Advance the reviewed source/trust files once more below.
 for(const file of reserved)write(file,'-- intermediate refreshed source integration\n');
 git(['add','.']);commit();
 const intermediateRefresh=git(['rev-parse','HEAD']);
 // The latest combined base can replace source proofs and registry descriptions.
 // The environment contribution must preserve that exact work.
 for(const file of reserved)write(file,'-- refreshed source integration\n');
 for(const file of ['Solidity.lean','docs/README.md','docs/module-map.md'])
  write(file,'-- retained registry entry\n-- refreshed base registry entry\n');
 git(['add','.']);commit();
 const refreshed=git(['rev-parse','HEAD']);
 const gateFile=join(fixture,'scripts/check-backend-environment.mjs');
 const gateSource=readFileSync(gateFile,'utf8');
 assert.ok(gateSource.includes("const integrationBase='b965d675e260a374401b131e59d501f8ce5da147';"));
 assert.ok(gateSource.includes("const refreshedBase='0e2a8ec34c6279853e1d9673b704735403341257';"));
 write('scripts/check-backend-environment.mjs',gateSource.replace(
  "const integrationBase='b965d675e260a374401b131e59d501f8ce5da147';",
  `const integrationBase='${boundary}';`).replace(
  "const refreshedBase='0e2a8ec34c6279853e1d9673b704735403341257';",
  `const refreshedBase='${refreshed}';`));
 git(['add','.']);commit();
 gate(null);
 gate(null,'--ownership-base',refreshed,'--ownership-head',git(['rev-parse','HEAD']));
 // Reproduce the review finding: the latest retained files fail if the gate
 // still pins an earlier refresh, even with an explicit ownership interval.
 const currentGate=readFileSync(gateFile,'utf8');
 for(const staleBase of [previousRefresh,intermediateRefresh]){
  write('scripts/check-backend-environment.mjs',currentGate.replace(
   `const refreshedBase='${refreshed}';`,`const refreshedBase='${staleBase}';`));
  gate(/integrated combined base file changed/);
  gate(/integrated combined base file changed/,'--ownership-base',refreshed,'--ownership-head',git(['rev-parse','HEAD']));
 }
 git(['restore','scripts/check-backend-environment.mjs']);
 // Reproduce the actual combined-validation failure with the exact temporary
 // serial configuration; arbitrary content and tracked copies remain forbidden.
 const config='.cloudvm-validation.toml';
 const serial='[[lean_lib]]\nname = "Fixture"\nweakLeanArgs = ["--tstack=131072", "-j1"]\n';
 write(config,serial);gate(null);
 for(const invalid of [serial.replace('-j1','-j2'),serial+'more = true\n',serial.replace('--tstack=131072','-DmaxHeartbeats=0')]){
  write(config,invalid);gate(/unexpected temporary validation config/);
 }
 rmSync(join(fixture,config));
 write('tests/backend-environment/config.txt',serial);
 symlinkSync('tests/backend-environment/config.txt',join(fixture,config));
 gate(/temporary validation config must be a regular file/);
 rmSync(join(fixture,config));rmSync(join(fixture,'tests/backend-environment/config.txt'));
 write(config,serial);git(['add',config]);gate(/unowned write .cloudvm-validation.toml/);
 commit();cleanGate(/unowned write .cloudvm-validation.toml/);
 git(['reset','--hard','HEAD^']);
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
 write('docs/README.md','-- retained registry entry\n-- refreshed base registry entry\n');gate(/shared registry is not append-only/);
 git(['reset','-q','HEAD','--','docs/README.md']);
 write('docs/README.md','-- retained registry entry\n-- refreshed base registry entry\n-- appended entry\n');gate(null);
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
 write('docs/README.md','-- retained registry entry\n-- refreshed base registry entry\n-- committed append\n');
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
  git(['rm',file]);commit();cleanGate(/integrated combined base file changed/);
  git(['reset','--hard',before]);
  for(const staleBase of [boundary,previousRefresh,intermediateRefresh]){
   write(file,git(['show',`${staleBase}:${file}`])+'\n');
   gate(/integrated combined base file changed/);
   git(['add',file]);commit();cleanGate(/integrated combined base file changed/);
   // Choosing a later ownership interval cannot bypass the refreshed-base pin.
   gate(/integrated combined base file changed/,'--ownership-base',before,'--ownership-head',git(['rev-parse','HEAD']));
   git(['reset','--hard',before]);
  }
 }
 const sourceFile=reserved[0];
 write(sourceFile,'-- changed source integration\n');gate(/integrated combined base file changed/);
 git(['add',sourceFile]);
 write(sourceFile,'-- refreshed source integration\n');gate(/unowned write/);
 git(['reset','--hard',before]);
 chmodSync(join(fixture,sourceFile),0o755);git(['add',sourceFile]);commit();
 cleanGate(/integrated combined base file changed/);git(['reset','--hard',before]);
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
 console.log('ownership regressions pass: advanced/refreshed integration bases, reserved source/trust blobs and modes, exact untracked serial config, tracked/changed/symlink config rejection, contribution range, live repairs, unowned writes/renames, registry deletion, default committed violations/appends, pinned scalar/storage blobs and modes, explicit range, frozen imports, closure, proof gate');
}finally{rmSync(fixture,{recursive:true,force:true});}
