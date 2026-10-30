#!/usr/bin/env node
// Extend the shared layer gate to this owned preparation lane without
// changing another lane's registry of core modules. Also check source
// independence and deterministic (untrusted) numeric compiler constants.
import { readFileSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { loadGraph, reach, findPath } from './import-fanout.mjs';
const {graph} = loadGraph();
const roots=[...graph.keys()].filter(m=>m.startsWith('Solidity.Backend.Scalar.')).sort();
const frontend=[/^Solidity\.Tools\.SolCases$/,
  /^Solidity\.Syntax\.(Elab|Quote|Splice)(\.|$)/,
  /^Solidity\.Calculus\.(Print[^.]*|Surface[^.]*|TacticSyntax|Quote|NamedTerm)(\.|$)/];
let bad=0;
for(const root of roots){
  for(const dep of reach(graph,root)) if(frontend.some(r=>r.test(dep))){
    console.error('LAYER '+findPath(graph,root,dep).join(' -> '));bad++;
  }
  const source=readFileSync(root.replaceAll('.','/')+'.lean','utf8');
  if(/\b(sorry|sorryAx|native_decide|implemented_by)\b|^\s*(?:private\s+)?axiom\s|set_option\s+(?:maxHeartbeats|maxRecDepth)/m.test(source)){
    console.error('TRUST '+root);bad++;
  }
}
for(const root of ['Solidity.AST','Solidity.Semantics.Ops','Solidity.Semantics.Run']){
  for(const dep of reach(graph,root)) if(dep.startsWith('Solidity.Backend.Scalar.')){
    console.error('SOURCE DEPENDENCE '+findPath(graph,root,dep).join(' -> '));bad++;
  }
}
const generated=spawnSync('python3',['scripts/backend-scalar-thresholds.py','--check'],{encoding:'utf8'});
process.stdout.write(generated.stdout??'');process.stderr.write(generated.stderr??'');
if(generated.status!==0) bad++;
console.log(`${roots.length} scalar roots, ${bad} layer/source/trust/generation findings`);
process.exit(bad?1:0);
