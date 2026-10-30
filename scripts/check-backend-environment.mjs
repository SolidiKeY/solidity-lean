#!/usr/bin/env node
// Task-local closure/ownership gate: the global layer checker has an exact core list.
import assert from 'node:assert/strict';
import {readFileSync,readdirSync} from 'node:fs';
import {execFileSync,spawnSync} from 'node:child_process';
import {loadGraph,reach} from './import-fanout.mjs';
const base='50658f41061b366d6e503d1e8a3a324a281e9fca';
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
  const existing=spawnSync('git',['cat-file','-e',`${base}:${dep.replaceAll('.','/')}.lean`],{stdio:'ignore'});
  assert.equal(existing.status,0,`${m} imports unavailable/new other lane ${dep}`);
 }
}
const shared=new Set(['Solidity.lean','docs/module-map.md','docs/README.md']);
const changed=execFileSync('git',['diff',base,'--name-only','--'],{encoding:'utf8'}).trim().split('\n').filter(Boolean);
for(const file of changed){
 assert.ok(file.startsWith('Solidity/Backend/Environment/')||file==='docs/feature-work/backend-environment-lowering.md'||
  file==='scripts/check-backend-environment.mjs'||file.startsWith('tests/backend-environment/')||shared.has(file),`unowned write ${file}`);
 if(shared.has(file)){
  const stat=execFileSync('git',['diff',base,'--numstat','--',file],{encoding:'utf8'}).trim().split('\t');
  assert.equal(stat[1],'0',`shared registry is not append-only: ${file}`);
 }
}
for(const file of readdirSync('Solidity/Backend/Environment').filter(n=>n.endsWith('.lean'))){
 const text=readFileSync('Solidity/Backend/Environment/'+file,'utf8');
 assert.ok(!/\bset_option\s+(maxHeartbeats|maxRecDepth)|\b(?:sorry|native_decide|implemented_by|axiom)\b/.test(
  text.replace(/\/-[\s\S]*?-\//g,'').replace(/--[^\n]*/g,'')),`proof shortcut/budget in ${file}`);
}
console.log(`${owned.length} owned modules: core closure, frozen-base imports, ownership and append-only registries pass`);
