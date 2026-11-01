#!/usr/bin/env node
// Parser/alias controls only: this NEVER substitutes for fresh Lean checking,
// actual builtin axiom reports or a complete source/toolchain-bound batch.
import {imports,scanFixtureImports} from './fixture-cache.mjs';
import {readFileSync,existsSync} from 'node:fs';
import assert from 'node:assert/strict';
const cases=[
 ['import Solidity.KeySort\n',['Solidity.KeySort']],
 ['/- import Bad.One /- import Bad.Two -/ -/\nimport Solidity.Evm.Machine\n',['Solidity.Evm.Machine']],
 ['-- import Bad.One\nimport Solidity.KeySort -- ignored\n',['Solidity.KeySort']],
 ['def text := "import Bad.One\\\" /-"\nimport Solidity.Evm.Machine\n',['Solidity.Evm.Machine']],
 ['import tests.«internal-flow».TupleMemoryCalls Solidity.Evm.Compiler\n',['tests.«internal-flow».TupleMemoryCalls','Solidity.Evm.Compiler']],
 ['def value := "import Bad.One"\n',[]],
 ['',[]],
];
let controls=0;
function check(text,wanted) {
 assert.deepEqual(scanFixtureImports(text),wanted);
 const first=imports(text);assert.deepEqual(first,wanted);
 first.length=0;first.push('poisoned.pending');
 const second=imports(text);assert.deepEqual(second,wanted);assert.notEqual(first,second);
 second.pop();assert.deepEqual(imports(text),wanted);
 const changed=text+'\nimport Solidity.Backend.InternalFlow.CallerView\n';
 assert.deepEqual(imports(changed),scanFixtureImports(changed));
 assert.deepEqual(imports(text),wanted);controls++;
}
for(const [text,wanted]of cases)check(text,wanted);
for(const bad of ['/- unclosed','"unclosed','/- outer /- nested -/']) {
 for(let n=0;n<2;n++)assert.throws(()=>imports(bad),/unclosed source comment\/string/);
 assert.throws(()=>scanFixtureImports(bad),/unclosed source comment\/string/);controls++;
}
// Exercise the actual complete current project-source graph named by every
// existing checked fixture binding, rather than inventing an import fixture AST.
const registry=JSON.parse(readFileSync('tests/internal-flow/fixture-axiom-pins.json','utf8')),paths=new Set();
for(const name of Object.keys(registry)) {
 const binding=JSON.parse(readFileSync(`.lake/build/lib/lean/tests/internal-flow/${name}.v12-cache.json`,'utf8'));
 for(const path of Object.keys(binding.inputs))if(path.endsWith('.lean')&&!path.startsWith('toolchain/')&&existsSync(path))paths.add(path);
}
for(const path of [...paths].sort()) {
 const text=readFileSync(path,'utf8');check(text,scanFixtureImports(text));
}
console.log(JSON.stringify({status:'pass',pure_parse_and_pending_array_controls:controls,actual_project_sources:paths.size,all_registered_bindings:Object.keys(registry).length,no_Lean_invocation:true,not_a_cache_source_or_axiom_gate:true}));
