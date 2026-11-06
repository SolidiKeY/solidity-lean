#!/usr/bin/env node
import {readFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {resolve,dirname} from 'node:path';
import {fileURLToPath} from 'node:url';
export const replayModules = ['Solidity.Calculus.MemoryLoopReplay',
  ...['Discover','Assemble'].flatMap(kind=>Array.from({length:10},(_,i)=>'Solidity.TestSuite.MemoryLoopReplay.'+kind+String(i).padStart(2,'0'))),
  'Solidity.TestSuite.Derived17MemoryLoop','Solidity.TestSuite.MemoryLoopReplay.Refusals','Solidity.TestSuite.Derived17'];
export function cumulativeTiming(result, hashSource) {
  const errors=[];
  if(!result || typeof result!=='object' || Array.isArray(result)) return ['invalid workload record'];
  if(result.kind!=='fresh-original-Derived17-workload' || result.exit_code!==0) errors.push('workload incomplete or failed');
  if(result.budgetSeconds!==300 || !(Number.isFinite(result.seconds) && result.seconds>=0 && result.seconds<=300)) errors.push('original cumulative 300-second workload budget exceeded or changed');
  if(!Array.isArray(result.checks)) errors.push('checks must be an array');
  const checks=Array.isArray(result.checks)?result.checks:[];
  if(checks.length!==replayModules.length || new Set(checks.map(x=>x.module)).size!==replayModules.length || replayModules.some(m=>!checks.some(x=>x.module===m))) errors.push('missing, duplicated or unexpected workload member');
  let sum=0;
  for(const c of checks) {
    if(c.fresh!==true || c.exit_code!==0 || !Number.isFinite(c.seconds) || c.seconds<0) errors.push('not freshly checked: '+c.module);
    if(Number.isFinite(c.seconds)) sum+=c.seconds;
    if(typeof c.sourceSha256!=='string' || !/^[a-f0-9]{64}$/.test(c.sourceSha256)) errors.push('invalid source hash');
    if(hashSource && replayModules.includes(c.module) && hashSource(c.module)!==c.sourceSha256) errors.push('source changed since fresh check: '+c.module);
  }
  if(sum>300 || sum>result.seconds+0.1) errors.push('cumulative member timing inconsistent or past300');
  return errors;
}
export function readTiming(path) {
  const root=resolve(dirname(fileURLToPath(import.meta.url)),'..');
  try {return cumulativeTiming(JSON.parse(readFileSync(path,'utf8')),module=>createHash('sha256').update(readFileSync(resolve(root,module.replaceAll('.','/')+'.lean'))).digest('hex'));}
  catch(e) {return ['unavailable fresh workload evidence: '+e.message];}
}
if(import.meta.url===`file://${process.argv[1]}`) {
  const errors=readTiming(process.argv[2]);
  console.log(errors.length?errors.join('\n'):'memory-loop timing: complete fresh original workload <=300s');
  process.exitCode=errors.length?1:0;
}
