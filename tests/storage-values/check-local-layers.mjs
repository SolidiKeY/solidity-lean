import { loadGraph, reach } from '../../scripts/import-fanout.mjs';
import { execFileSync } from 'node:child_process';
const { graph } = loadGraph();
const owned = [...graph.keys()].filter(x => x.startsWith('Solidity.Storage.Representation.'));
const baseline = new Set(execFileSync('git', ['ls-tree','-r','--name-only',
  '50658f41061b366d6e503d1e8a3a324a281e9fca','Solidity'], {encoding:'utf8'})
  .trim().split('\n').filter(x => x.endsWith('.lean')).map(x => x.slice(0,-5).replaceAll('/','.')));
const forbidden = /^Solidity\.(Frontend|Evm|Examples|Tools|Solkey|TestSuite|Corpus)(\.|$)|^Solidity\.Syntax\.(Elab|Quote|Splice)(\.|$)|^Solidity\.Calculus\.(Print|Surface|TacticSyntax|Quote|NamedTerm)/;
let failures = 0;
for (const m of owned) for (const d of reach(graph,m)) {
  if (forbidden.test(d) || (!baseline.has(d) && !owned.includes(d))) {
    console.log(`forbidden or uncommitted-lane dependency: ${m} -> ${d}`); failures++;
  }
}
console.log(`${owned.length} owned modules; ${failures} forbidden or other-new-lane dependencies`);
process.exitCode = failures ? 1 : 0;
