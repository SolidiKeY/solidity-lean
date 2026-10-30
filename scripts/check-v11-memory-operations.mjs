#!/usr/bin/env node
// Check this lane's import boundary without changing the shared CORE registry.
import { loadGraph, reach, findPath } from './import-fanout.mjs';
import { readFileSync } from 'node:fs';
const { graph } = loadGraph();
const owned = [...graph.keys()].filter(m => m.startsWith('Solidity.Backend.MemoryOps.'));
const forbidden = /^(Solidity\.Syntax\.(Elab|Quote|Splice)(\.|$)|Solidity\.Calculus\.(Print[^.]*|Surface[^.]*|TacticSyntax|Quote|NamedTerm)(\.|$)|Solidity\.Tools\.SolCases$|Solidity\.Backend\.(Scalar|Storage|Environment|Failure|Creation)\.)/;
const root = readFileSync('Solidity.lean', 'utf8').split('\n').filter(l => l.startsWith('import ')).map(l => l.split(/\s+/)[1]);
const registered = new Set(root.flatMap(m => [m, ...reach(graph,m)]));
let bad = 0;
for (const m of owned) {
  if (!registered.has(m)) { console.error(`Unregistered: ${m}`); bad++; }
  for (const dep of reach(graph,m)) if (forbidden.test(dep)) {
    console.error(findPath(graph,m,dep).join(' -> ')); bad++;
  }
}
console.log(`${owned.length} V11 modules, ${bad} boundary/registration findings`);
process.exit(bad || owned.length === 0 ? 1 : 0);
