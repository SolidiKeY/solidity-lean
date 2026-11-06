// Reuse the unchanged benchmark conversion and compiler; never reuse verdicts.
import {prepare, validateInputs} from '../../../scripts/testsuite-performance.mjs';
import fs from 'node:fs';
import path from 'node:path';
import {createHash} from 'node:crypto';
const directory=path.resolve('docs/benchmarks/directruntime-2026-11-04/before/inputs');
if(fs.existsSync(path.join(directory,'inputs.json')))throw new Error('Baseline inputs already exist; refusing overwrite');
const inputs=await prepare(directory);
validateInputs(inputs);
if(inputs.count!==83)throw new Error(`Expected 83 functions, got ${inputs.count}`);
const files=['scripts/testsuite-performance.mjs','scripts/check-direct-testsuite.mjs',
 'web/test/testsuite-performance.cjs','scripts/build-direct-native.py',
 'scripts/build-direct-runtime.py','scripts/direct-runtime-closure.py',
 'web/browser/direct-bridge.c','lean-toolchain'];
const identities=Object.fromEntries(files.map(file=>[file,createHash('sha256').update(fs.readFileSync(file)).digest('hex')]));
fs.writeFileSync(path.join(directory,'harness-identities.json'),JSON.stringify(identities,null,2)+'\n');
console.log(JSON.stringify({count:inputs.count,inventorySha256:inputs.inventorySha256,directory,verdicts:0}));
