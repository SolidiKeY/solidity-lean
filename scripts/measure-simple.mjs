#!/usr/bin/env node
// Prepare the same source bytes used by the browser benchmark. Native Lean
// runs one fresh proof per namespace in a single process, retaining imports.
import fs from 'node:fs';
import path from 'node:path';
import {createRequire} from 'node:module';
import {compileFixture} from './solc-ast.mjs';
const require=createRequire(import.meta.url),cases=require('../web/test/simple-programs.cjs');
const directory=path.resolve(process.argv[2]||'.lake/simple-measurement');
const repeats=Number(process.env.BENCH_REPEATS||3);
if(!Number.isSafeInteger(repeats)||repeats<=0)throw new Error('Invalid BENCH_REPEATS');
fs.mkdirSync(directory,{recursive:true});
const solkeyRoot=path.resolve(process.env.SOLKEY_ROOT||'tests/migration/solkey');
const soljsonDir=process.env.SOLJSON_DIR||path.join(solkeyRoot,'keyext.solidity.core/build/soljson');
const trials=[];
let wrapper='import Solidity.Frontend.Testing\nset_option sol.benchmark true\n'+(process.env.BENCH_TACTICS==='1'?'set_option sol.benchmark.tactics true\n':'');
for(let repeat=0;repeat<repeats;repeat++)for(const example of cases){
  const stem=`${example.name}-${repeat}`,source=path.join(directory,stem+'.sol'),fixture=path.join(directory,stem+'.ast.json');
  fs.writeFileSync(source,example.source+`\n// measurement repetition ${repeat}\n`);
  const start=performance.now();
  const compiled=compileFixture({quiet:true,args:['--source',source,'--out',fixture,'--no-wrapper',
    '--solkey',solkeyRoot,'--soljson',soljsonDir]});
  const namespace=`Bench.C${trials.length}.Simple`,output=path.join(directory,stem+'.result.json');
  wrapper+=`#solkey_benchmark ${JSON.stringify(stem+':import')} in solc_import ${JSON.stringify(fixture)} hash ${compiled.hash} as ${namespace} testing\n`;
  wrapper+=`#solkey_benchmark ${JSON.stringify(stem+':obligations')} in solc_scoped_problems ${namespace} decl\n`;
  wrapper+=`#solkey_benchmark ${JSON.stringify(stem+':test')} in #solkey_test ${namespace} to ${JSON.stringify(output)}\n`;
  trials.push({name:example.name,repeat,status:example.status,source,fixture,output,sourceHash:compiled.sourceHash,compilationMs:performance.now()-start});
}
fs.writeFileSync(path.join(directory,'Native.lean'),wrapper);
fs.writeFileSync(path.join(directory,'inputs.json'),JSON.stringify({repeats,trials},null,2)+'\n');
console.log(`Prepared ${trials.length} identical source programs in ${directory}`);
