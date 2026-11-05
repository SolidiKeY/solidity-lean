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
if(!original.equals(execFileSync('git',['show','8bf8321873befa3f35ca31e97e5339a1baee93e6:'+shared],{cwd:root,maxBuffer:original.length+65536})))throw Error('shared registry differs from authorized published adoption');
const {collect,compare,STANDARD}=await import(pathToFileURL(join(root,'scripts/check-axiom-pins.mjs')));
const recorded=JSON.parse(original),found=collect(root),before=compare(found,recorded);
if(before.errors.length)throw Error(JSON.stringify(before.errors));
const local=JSON.parse(readFileSync(join(here,'axiom-pins.json'))).theorems;
const delta={};
for(const [key,pin] of found){
 if(Object.hasOwn(recorded,key))continue;
 if(pin.file!==pinFile||!Object.hasOwn(local,pin.name))throw Error('unexpected unrecorded pin:'+key);
 if(JSON.stringify([...local[pin.name]].sort())!==JSON.stringify(pin.axioms))throw Error('local/kernel guard set differs:'+key);
 if(pin.axioms.some(x=>!STANDARD.includes(x)))throw Error('nonstandard axiom');
 delta[key]=pin.axioms;
}
if(Object.keys(delta).length!==414||before.notes.length!==414)throw Error('expected exact414 pin delta');
const merged={...recorded,...delta};
for(const [key,value] of Object.entries(recorded))if(JSON.stringify(value)!==JSON.stringify(merged[key]))throw Error('old record changed');
const after=compare(found,merged);if(after.errors.length||after.notes.length)throw Error('candidate comparison failed');
const candidate=JSON.stringify(Object.fromEntries(Object.entries(merged).sort(([a],[b])=>a.localeCompare(b))),null,1)+'\n';
mkdirSync(out,{recursive:true});
const save=(name,value)=>writeFileSync(join(out,name),value,{flag:'wx'});
save('shared-registry.candidate.json',candidate);
save('pin-delta.json',JSON.stringify(delta,null,2)+'\n');
save('comparison.json',JSON.stringify({command:['node',self,out],generator_sha256:sha(readFileSync(self)),source_head:execFileSync('git',['rev-parse','HEAD'],{cwd:root}).toString().trim(),base:'6f3eedf0788ee1f8a3bcf230558c712ecdca04d5',registry_base:'8bf8321873befa3f35ca31e97e5339a1baee93e6',shared_inventory:shared,shared_inventory_sha256:sha(original),source_pins:pinFile,source_pins_sha256:sha(readFileSync(join(root,pinFile))),old_count:Object.keys(recorded).length,added_count:Object.keys(delta).length,candidate_count:Object.keys(merged).length,old_entries_unchanged:true,before,after,candidate_sha256:sha(candidate),boundary:'UNAPPLIED proposal only. Global full gate remains failed until authorized registration. No shared file, checker, theorem, premise, exclusion, axiom set, observation or budget changed.'},null,2)+'\n');
console.log('PROPOSAL_ONLY: preserved '+Object.keys(recorded).length+' old entries; exact414 additions; candidate comparison0errors/0notes; shared registry UNCHANGED');
