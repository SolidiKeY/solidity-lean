#!/usr/bin/env node
// Task-local closure/ownership gate: the global layer checker has an exact core list.
import assert from 'node:assert/strict';
import {readFileSync,readdirSync} from 'node:fs';
import {execFileSync,spawnSync} from 'node:child_process';
import {parseArgs} from 'node:util';
import {loadGraph,reach} from './import-fanout.mjs';
// Dependency availability is frozen even when the reviewed ownership range changes.
const dependencyBase='50658f41061b366d6e503d1e8a3a324a281e9fca';
const sourceHead='93e97b28e61f1466eafeb6163baed9da1f9e8240';
const {values}=parseArgs({options:{'ownership-base':{type:'string'},'ownership-head':{type:'string'}}});
assert.equal(Boolean(values['ownership-base']),Boolean(values['ownership-head']),
 'supply both --ownership-base and --ownership-head');
const ownershipBase=values['ownership-base']??dependencyBase;
const ownershipHead=values['ownership-head']??sourceHead;
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
function checkOwnership(range){
 const changed=paths(git(['diff','--no-renames','--name-only','-z',...range,'--']));
 for(const file of changed){
  checkOwned(file);
  if(shared.has(file)){
   const stat=git(['diff','--no-renames','--numstat',...range,'--',file]).trim().split('\t');
   assert.equal(stat[1],'0',`shared registry is not append-only: ${file}`);
  }
 }
}
// Audit the complete contribution, rather than attributing other integrated lanes
// to this worker. Audit the index and worktree independently against HEAD, so
// an unstaged restoration cannot hide a staged ownership/registry violation.
checkOwnership([ownershipBase,ownershipHead]);
checkOwnership(['--cached','HEAD']);
checkOwnership(['HEAD']);
for(const file of paths(git(['ls-files','--others','--exclude-standard','-z'])))
 checkOwned(file);
for(const file of readdirSync('Solidity/Backend/Environment').filter(n=>n.endsWith('.lean'))){
 const text=readFileSync('Solidity/Backend/Environment/'+file,'utf8');
 assert.ok(!/\bset_option\s+(maxHeartbeats|maxRecDepth)|\b(?:sorry|native_decide|implemented_by|axiom)\b/.test(
  text.replace(/\/-[\s\S]*?-\//g,'').replace(/--[^\n]*/g,'')),`proof shortcut/budget in ${file}`);
}
console.log(`${owned.length} owned modules: core closure, frozen-base imports, ownership ${ownershipBase}..${ownershipHead}, working repairs and append-only registries pass`);
