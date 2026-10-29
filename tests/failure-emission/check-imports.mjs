// Task-local closure audit supplements the shared core list without editing it.
import {execFileSync} from 'node:child_process';
import {loadGraph, reach} from '../../scripts/import-fanout.mjs';
const base='50658f41061b366d6e503d1e8a3a324a281e9fca';
const baseModules=new Set(execFileSync('git',['ls-tree','-r','--name-only',base,'Solidity'],{encoding:'utf8'}).trim().split('\n').filter(x=>x.endsWith('.lean')).map(x=>x.slice(0,-5).replaceAll('/','.')));
const {graph}=loadGraph();
const owned=m=>m.startsWith('Solidity.Backend.Failure.');
const forbidden=m=>/^Solidity\.(Source|Frontend|Evm)\./.test(m)||/^Solidity\.Syntax\.(Elab|Quote|Splice)(\.|$)/.test(m)||/^Solidity\.Calculus\.(Print|Surface|TacticSyntax|Quote|NamedTerm)/.test(m);
const findings=[];const modules=[...graph.keys()].filter(owned);
for(const m of modules){
 for(const d of graph.get(m))if(!owned(d)&&!baseModules.has(d))findings.push(`${m}: non-base external lane ${d}`);
 for(const d of reach(graph,m))if(forbidden(d))findings.push(`${m}: forbidden closure ${d}`);
}
for(const d of reach(graph,'Solidity.Backend.Failure.Slice'))if(owned(d))findings.push(`independent Slice reaches emitter-lane definition ${d}`);
for(const d of reach(graph,'Solidity.Backend.Failure.Checkpoint'))if(owned(d)&&d!=='Solidity.Backend.Failure.Slice')findings.push(`independent Checkpoint reaches emitter ${d}`);
for(const d of reach(graph,'Solidity.Backend.Failure.Gap'))if(owned(d))findings.push(`base-only gap reaches new implementation ${d}`);
console.log(`${modules.length} failure modules, ${findings.length} import/independence findings`);
for(const f of findings)console.error(f);
process.exitCode=findings.length?1:0;
