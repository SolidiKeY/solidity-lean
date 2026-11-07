// Read-only central inventory census; writes only an explicitly selected off-Git coordinator ticket.
// Does not update pins, statements, axioms, exclusions or generated fragments.
import {readFileSync,writeFileSync,realpathSync,constants} from 'node:fs';
import path from 'node:path';
import {fileURLToPath} from 'node:url';
import {createHash} from 'node:crypto';
import {collect,compare} from '../../../check-axiom-pins.mjs';
const root=path.resolve(path.dirname(fileURLToPath(import.meta.url)),'../../../..');
const args=process.argv.slice(2);
if(args.length!==2||args[0]!=='--output')throw Error('Usage: propose_pin_sync.mjs --output EXTERNAL_PATH');
const output=path.resolve(args[1]);
function requireExternal(file){
 if(!path.relative(root,file).startsWith('..'+path.sep))throw Error('H44 bulk ticket must stay outside Git');
}
requireExternal(output);
// The external parent must already exist; do not create directories through symlinks.
const destination=path.join(realpathSync(path.dirname(output)),path.basename(output));
requireExternal(destination);
const central='scripts/g07-axiom-pins.json',bytes=readFileSync(path.join(root,central));
const integration=readFileSync(path.join(root,'scripts/h62/item2/audit-abi-world/prepare_resume_config.py'),'utf8').match(/^INTEGRATION="([a-f0-9]{40})"/m)[1];
const recorded=JSON.parse(bytes),found=collect(root),result=compare(found,recorded);
if(result.errors.length)throw Error('Nonstandard/growing/missing pins require separate owner analysis: '+JSON.stringify(result.errors));
const changes=[...found].filter(([key,value])=>JSON.stringify(recorded[key])!==JSON.stringify(value.axioms)).sort(([a],[b])=>a.localeCompare(b)).map(([key,value])=>({key,previous:recorded[key]??null,actual_axioms:value.axioms}));
const ticket={schema_version:1,id:'PIN-'+integration.slice(0,8),owner:'coordinator / G07 inventory fragment owners',central_file:central,central_sha256:createHash('sha256').update(bytes).digest('hex'),integration,source_pins:found.size,nonstandard_or_growth_errors:result.errors,unrecorded_changes:changes.length,changes,
 action:'Owner reviews and records the existing standard-only pins in its per-file fragments, then regenerates the central inventory. No Lean statement, proof, axiom set, premise or exclusion changes.',
 blocked_by:'Original audit instruction: no generated roots, central module maps or axiom pin edits; supply registration fragments to coordinator.',
 options:['Coordinator applies reviewed existing-pin metadata delta and publishes it; worker reruns the inventory gate.','Keep inventory frozen and retain the final validation blocker with this complete handoff.']};
writeFileSync(destination,JSON.stringify(ticket,null,2)+'\n',
 {flag:constants.O_WRONLY|constants.O_CREAT|constants.O_TRUNC|constants.O_NOFOLLOW});
console.log(JSON.stringify({ticket:output,source_pins:found.size,unrecorded_changes:changes.length,errors:result.errors.length}));
