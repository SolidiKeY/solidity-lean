// Read-only central inventory census; writes only an owned coordinator ticket.
// Does not update pins, statements, axioms, exclusions or generated fragments.
import {readFileSync,writeFileSync,mkdirSync} from 'node:fs';
import path from 'node:path';
import {fileURLToPath} from 'node:url';
import {createHash} from 'node:crypto';
import {collect,compare} from '../../../check-axiom-pins.mjs';
const root=path.resolve(path.dirname(fileURLToPath(import.meta.url)),'../../../..');
const relative='tests/h62/item2/audit-abi-world/handoff/resumed/axiom-pin-owner-ticket.json';
const central='scripts/g07-axiom-pins.json',bytes=readFileSync(path.join(root,central));
const recorded=JSON.parse(bytes),found=collect(root),result=compare(found,recorded);
if(result.errors.length)throw Error('Nonstandard/growing/missing pins require separate owner analysis: '+JSON.stringify(result.errors));
const changes=[...found].filter(([key,value])=>JSON.stringify(recorded[key])!==JSON.stringify(value.axioms)).sort(([a],[b])=>a.localeCompare(b)).map(([key,value])=>({key,previous:recorded[key]??null,actual_axioms:value.axioms}));
const ticket={schema_version:1,id:'PIN-706',owner:'coordinator / G07 inventory fragment owners',central_file:central,central_sha256:createHash('sha256').update(bytes).digest('hex'),integration:'706e36825929d6d0084dc08b88de9349abcd25aa',source_pins:found.size,nonstandard_or_growth_errors:result.errors,unrecorded_changes:changes.length,changes,
 action:'Owner reviews and records the existing standard-only pins in its per-file fragments, then regenerates the central inventory. No Lean statement, proof, axiom set, premise or exclusion changes.',
 blocked_by:'Original audit instruction: no generated roots, central module maps or axiom pin edits; supply registration fragments to coordinator.',
 options:['Coordinator applies reviewed existing-pin metadata delta and publishes it; worker reruns the inventory gate.','Keep inventory frozen and retain the final validation blocker with this complete handoff.']};
mkdirSync(path.dirname(path.join(root,relative)),{recursive:true});writeFileSync(path.join(root,relative),JSON.stringify(ticket,null,2)+'\n');
console.log(JSON.stringify({ticket:relative,source_pins:found.size,unrecorded_changes:changes.length,errors:result.errors.length}));
