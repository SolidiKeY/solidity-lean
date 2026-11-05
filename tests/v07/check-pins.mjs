import {readFileSync,readdirSync} from 'node:fs';
import {fileURLToPath} from 'node:url';
import {resolve} from 'node:path';
import {blankLean} from '../../scripts/check-trust.mjs';
import {pins,STANDARD} from '../../scripts/check-axiom-pins.mjs';
export function compareExact(actual,expected,names) {
 const errors=[];
 for(const n of new Set([...Object.keys(actual),...Object.keys(expected),...names])) {
  if(!names.includes(n)||!Object.hasOwn(actual,n)||!Object.hasOwn(expected,n)) errors.push(`missing/unexpected ${n}`);
  else if(JSON.stringify([...actual[n]].sort())!==JSON.stringify([...expected[n]].sort()) || actual[n].some(a=>!STANDARD.includes(a))) errors.push(`changed axioms ${n}`);
 }
 return errors;
}
// Closed proof clients are definitions, not additional general theorems.
// Include every exported client in the registered client families.
const clientDefs=JSON.parse(readFileSync('tests/v07/proof-clients.json','utf8'));
export function ownedNames() {
 const names=[];
 for(const f of readdirSync('Solidity/Lowering/V07').filter(f=>f.endsWith('.lean')).sort()) {
  const stack=[];
  const text=blankLean(readFileSync('Solidity/Lowering/V07/'+f,'utf8'));
  for(const line of text.split('\n')) {
   const ns=line.match(/^namespace ([A-Za-z_][A-Za-z0-9_.']*)\s*$/);
   if(ns){stack.push(ns[1]);continue;}
   if(/^end(?:\s+[A-Za-z_][A-Za-z0-9_.']*)?\s*$/.test(line)) {if(!stack.length)throw new Error('unmatched namespace '+f);stack.pop();continue;}
   const client=clientDefs[f] ?? [];
   const th=line.match(/^(?:private |protected )?theorem (\S+)/) ?? (client.includes(line.match(/^def (\S+)/)?.[1]) ? line.match(/^def (\S+)/) : null);
   if(th) {
    if(!stack.length||!/^([A-Za-z_][A-Za-z0-9_']*)(\.[A-Za-z_][A-Za-z0-9_']*)*$/.test(th[1]))throw new Error('unsupported theorem '+f+': '+line);
    if(line.startsWith('private '))throw new Error('private theorem requires explicit pin support '+f);
    names.push(stack.join('.')+'.'+th[1]);
   }
  }
  if(stack.length)throw new Error('unclosed namespace '+f);
 }
 if(new Set(names).size!==names.length)throw new Error('duplicate theorem declaration');
 return names;
}
if(process.argv[1] && resolve(process.argv[1])===fileURLToPath(import.meta.url)) {
 const args=process.argv.slice(2);
 if(args.length!==0 && args.length!==2)throw new Error('usage: check-pins.mjs [GUARDS REGISTRY]');
 const [guardPath,registryPath]=args.length?args:['tests/v07/Axioms.lean','tests/v07/axiom-pins.json'];
 const names=ownedNames();
 const found=pins(readFileSync(guardPath,'utf8'));
 const actual={};const errors=[];
 for(const p of found) {
  if(Object.hasOwn(actual,p.name))errors.push('duplicate '+p.name);
  if(p.axioms===null || p.target!==p.name) errors.push('malformed '+p.name);
  actual[p.name]=p.axioms??[];
 }
 errors.push(...compareExact(actual,JSON.parse(readFileSync(registryPath,'utf8')),names));
 if(errors.length){console.error(errors.join('\n'));process.exitCode=1;}
 else console.log(`V07 exact axiom registry: ${names.length} proof exports, ${found.length} guards`);
}
