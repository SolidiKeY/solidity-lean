#!/usr/bin/env node
// Task-local closure/ownership gate: the global layer checker has an exact core list.
import assert from 'node:assert/strict';
import {lstatSync,readFileSync,readdirSync} from 'node:fs';
import {execFileSync,spawnSync} from 'node:child_process';
import {parseArgs} from 'node:util';
import {loadGraph,reach} from './import-fanout.mjs';
// Dependency availability is frozen even when the reviewed ownership range changes.
const dependencyBase='50658f41061b366d6e503d1e8a3a324a281e9fca';
const sourceHead='93e97b28e61f1466eafeb6163baed9da1f9e8240';
const integrationBase='b965d675e260a374401b131e59d501f8ce5da147';
// The coordinator refreshed the combined base with further source soundness work.
// Audit the complete requested interval, pinning these contributions separately.
const refreshedBase='37f572e8d954f2c697eeb3cda7a1a0206fd33c89';
// Other integrated contributions are read-only, pinned by exact blob and mode.
const scalarBase='8445c3fc203144251b9d1fc9181f7f61a8189522';
const scalarHead='2a267e4f5f43b87d7e49ae14685082559706a03d';
const storageHead='8db4c673cd2d0c434221cbf5d398e1a92cf7ea4f';
const {values}=parseArgs({options:{'ownership-base':{type:'string'},'ownership-head':{type:'string'}}});
assert.equal(Boolean(values['ownership-base']),Boolean(values['ownership-head']),
 'supply both --ownership-base and --ownership-head');
const ownershipBase=values['ownership-base']??integrationBase;
// An omitted head audits the current candidate, including uncommitted repairs.
const ownershipHead=values['ownership-head'];
const prefix='Solidity.Backend.Environment.';
const {graph}=loadGraph();
const owned=[...graph.keys()].filter(m=>m.startsWith(prefix));
assert.ok(owned.length>=11,'owned modules must be registered');
const forbidden=/^Solidity\.(Frontend|Source|Tools|Examples|TestSuite|Calculus\.(Print|Surface|Tactic|NamedTerm|Quote)|Syntax\.(Elab|Quote|Splice))|^SolidityBridge\./;
for(const m of owned){
 for(const dep of reach(graph,m))assert.ok(!forbidden.test(dep),`${m} reaches frontend/external lane ${dep}`);
 const file=m.replaceAll('.','/')+'.lean';
 for(const [,dep] of readFileSync(file,'utf8').matchAll(/^import\s+(\S+)/gm)){
  if(dep.startsWith(prefix)||dep.startsWith('Lean.'))continue;
  const existing=spawnSync('git',['cat-file','-e',`${dependencyBase}:${dep.replaceAll('.','/')}.lean`],{stdio:'ignore'});
  assert.equal(existing.status,0,`${m} imports unavailable/new other lane ${dep}`);
 }
}
const shared=new Set(['Solidity.lean','docs/module-map.md','docs/README.md']);
const git=args=>execFileSync('git',args,{encoding:'utf8'});
const paths=text=>text.split('\0').filter(Boolean);
function checkOwned(file){
 assert.ok(file.startsWith('Solidity/Backend/Environment/')||file==='docs/feature-work/backend-environment-lowering.md'||
  file==='scripts/check-backend-environment.mjs'||file.startsWith('tests/backend-environment/')||shared.has(file),`unowned write ${file}`);
}
const integratedFiles=new Map();
for(const {name,base,head,files} of [
 {name:'scalar',base:scalarBase,head:scalarHead,files:[
  'Solidity/Backend/Scalar/','docs/feature-work/backend-scalar-lowering.md',
  'scripts/backend-scalar-thresholds.py','scripts/check-backend-scalar.mjs',
  'scripts/check-backend-scalar-evm.mjs','scripts/fixtures/backend-scalar-export.lean']},
 {name:'storage',base:integrationBase,head:storageHead,files:[
  'Solidity/Storage/Representation/','docs/feature-work/storage-value-representation.md',
  'tests/storage-values/','docs/feature-work/backend-failure-emission.md']}
]){
 for(const file of paths(git(['diff','--no-renames','--name-only','-z',base,head,'--',...files])))
  integratedFiles.set(file,{name,head});
}
for(const file of paths(git(['diff','--no-renames','--name-only','-z',integrationBase,refreshedBase,'--'])))
 if(!shared.has(file))integratedFiles.set(file,{name:'combined base',head:refreshedBase});
function checkOwnership(range,{integrated=false,registryRange=range}={}){
 const changed=paths(git(['diff','--no-renames','--name-only','-z',...range,'--']));
 for(const file of changed){
  if(integrated&&integratedFiles.has(file)){
   const pin=integratedFiles.get(file);
   const endpoint=ownershipHead?[ownershipHead]:[];
   assert.equal(git(['diff','--no-ext-diff','--no-renames',pin.head,...endpoint,'--',file]),'',
    `integrated ${pin.name} file changed: ${file}`);
   continue;
  }
  checkOwned(file);
  if(shared.has(file)){
   const stat=git(['diff','--no-renames','--numstat',...registryRange,'--',file]).trim();
   assert.ok(stat===''||stat.split('\t')[1]==='0',`shared registry is not append-only: ${file}`);
  }
 }
}
// Preserve the original lane audit, then include all committed integration repairs.
// Other lanes qualify only through the exact pinned contributions above.
checkOwnership([dependencyBase,sourceHead]);
checkOwnership([ownershipBase,...(ownershipHead?[ownershipHead]:[])],{
 integrated:true,registryRange:[refreshedBase,...(ownershipHead?[ownershipHead]:[])]});
// A complete revert to the older boundary disappears from that range. Also
// compare the refreshed base so removing its contributions cannot hide there.
checkOwnership([refreshedBase,...(ownershipHead?[ownershipHead]:[])],{integrated:true});
// Also reject staged violations concealed by an unstaged restoration.
checkOwnership(['--cached','HEAD'],{registryRange:['--cached',refreshedBase]});
checkOwnership(['HEAD'],{registryRange:[refreshedBase]});
for(const file of paths(git(['ls-files','--others','--exclude-standard','-z']))){
 if(file==='.cloudvm-validation.toml'){
  // This untracked input exists during the coordinator's gates. Do not grant
  // ownership to arbitrary config changes, symlinks, or a staged/committed copy.
  assert.ok(lstatSync(file).isFile(),'temporary validation config must be a regular file');
  let count=0;
  const serial=readFileSync('lakefile.toml','utf8').replace(/weakLeanArgs\s*=\s*\[([^\]]*)\]/g,(_,args)=>{
   count++;
   return 'weakLeanArgs = ['+args.trimEnd().replace(/,$/,'')+', "-j1"]';
  });
  assert.ok(count>0,'temporary validation config requires library arguments');
  assert.equal(readFileSync(file,'utf8'),serial,'unexpected temporary validation config');
 }else checkOwned(file);
}
for(const file of readdirSync('Solidity/Backend/Environment').filter(n=>n.endsWith('.lean'))){
 const text=readFileSync('Solidity/Backend/Environment/'+file,'utf8');
 assert.ok(!/\bset_option\s+(maxHeartbeats|maxRecDepth)|\b(?:sorry|native_decide|implemented_by|axiom)\b/.test(
  text.replace(/\/-[\s\S]*?-\//g,'').replace(/--[^\n]*/g,'')),`proof shortcut/budget in ${file}`);
}
console.log(`${owned.length} owned modules: core closure, frozen-base imports, ownership ${ownershipBase}..${ownershipHead??'worktree'}, working repairs and append-only registries pass`);
