#!/usr/bin/env node
// Read-only source collection; writes an UNAPPLIED integration proposal only.
import {readFileSync,writeFileSync,mkdirSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {dirname,resolve,join} from 'node:path';
import {fileURLToPath,pathToFileURL} from 'node:url';
import {execFileSync} from 'node:child_process';
const self=fileURLToPath(import.meta.url),here=dirname(self),root=resolve(here,'../../..');
const out=resolve(process.argv[2]||join(here,'pin-proposal'));
if(!out.startsWith(here+'/'))throw Error('output outside owned scope');
const sha=x=>createHash('sha256').update(x).digest('hex');
const shared='scripts/g07-axiom-pins.json',pinFile='tests/h28-sol/non-vacuity/lean/Solidity/Assurance/NonVacuityH28/Pins.lean';
const original=readFileSync(join(root,shared));
if(!original.equals(execFileSync('git',['show','e6849d3bdf516099d20c33d3581d523449764018:'+shared],{cwd:root,maxBuffer:original.length+65536})))throw Error('shared registry differs from authorized published adoption');
const {collect,compare,STANDARD}=await import(pathToFileURL(join(root,'scripts/check-axiom-pins.mjs')));
const recorded=JSON.parse(original),found=collect(root),before=compare(found,recorded);
if(before.errors.length)throw Error(JSON.stringify(before.errors));
const local=JSON.parse(readFileSync(join(here,'axiom-pins.json'))).theorems;
const delta={},external={};
for(const [key,pin] of found){
 if(Object.hasOwn(recorded,key))continue;
 if(pin.file!==pinFile){
  if(pin.file.startsWith('tests/h28-sol/non-vacuity/'))throw Error('unexpected owned pin:'+key);
  const source=readFileSync(join(root,pin.file));
  if(!source.equals(execFileSync('git',['show','e6849d3bdf516099d20c33d3581d523449764018:'+pin.file],{cwd:root,maxBuffer:source.length+65536})))throw Error('external source differs from adopted master:'+key);
  external[key]={axioms:pin.axioms,source_sha256:sha(source)};
  continue;
 }
 if(!Object.hasOwn(local,pin.name))throw Error('unexpected owned theorem:'+key);
 if(JSON.stringify([...local[pin.name]].sort())!==JSON.stringify(pin.axioms))throw Error('local/kernel guard set differs:'+key);
 if(pin.axioms.some(x=>!STANDARD.includes(x)))throw Error('nonstandard axiom');
 delta[key]=pin.axioms;
}
if(Object.keys(delta).length!==431)throw Error('expected exact431 owned pin delta');
const merged={...recorded,...delta};
for(const [key,value] of Object.entries(recorded))if(JSON.stringify(value)!==JSON.stringify(merged[key]))throw Error('old record changed');
const after=compare(found,merged),baselineFound=new Map(found);
for(const key of Object.keys(delta))baselineFound.delete(key);
const baselineDrift=compare(baselineFound,recorded);
if(after.errors.length||baselineDrift.errors.length||JSON.stringify(after.notes)!==JSON.stringify(baselineDrift.notes)||before.notes.length-after.notes.length!==431)throw Error('candidate changed external drift or failed to resolve exact owned delta');
const candidate=JSON.stringify(Object.fromEntries(Object.entries(merged).sort(([a],[b])=>a.localeCompare(b))),null,1)+'\n';
mkdirSync(out,{recursive:true});
const save=(name,value)=>writeFileSync(join(out,name),value,{flag:'wx'});
save('shared-registry.candidate.json',candidate);
save('pin-delta.json',JSON.stringify(delta,null,2)+'\n');
save('external-unregistered.json',JSON.stringify(external,null,2)+'\n');
save('comparison.json',JSON.stringify({command:['node',self,out],generator_sha256:sha(readFileSync(self)),source_head:execFileSync('git',['rev-parse','HEAD'],{cwd:root}).toString().trim(),base:'6f3eedf0788ee1f8a3bcf230558c712ecdca04d5',registry_base:'e6849d3bdf516099d20c33d3581d523449764018',shared_inventory:shared,shared_inventory_sha256:sha(original),source_pins:pinFile,source_pins_sha256:sha(readFileSync(join(root,pinFile))),old_count:Object.keys(recorded).length,added_count:Object.keys(delta).length,candidate_count:Object.keys(merged).length,old_entries_unchanged:true,external_unregistered_count:Object.keys(external).length,before,after,candidate_sha256:sha(candidate),boundary:'UNAPPLIED proposal only. Global full gate remains failed until authorized registration. No shared file, checker, theorem, premise, exclusion, axiom set, observation or budget changed.'},null,2)+'\n');
console.log('PROPOSAL_ONLY: preserved '+Object.keys(recorded).length+' old entries; exact431 owned additions; candidate comparison0errors/'+after.notes.length+' external notes; shared registry UNCHANGED');
