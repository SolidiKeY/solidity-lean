import {compileFixture} from '../../../scripts/solc-ast.mjs';
import {readFileSync,writeFileSync,mkdirSync} from 'node:fs';
import {dirname,join} from 'node:path';
import {fileURLToPath} from 'node:url';
import {createHash} from 'node:crypto';
import assert from 'node:assert/strict';
const root=dirname(fileURLToPath(import.meta.url));
const sha=b=>createHash('sha256').update(b).digest('hex');
function* walk(x){if(x&&typeof x==='object'){yield x;for(const v of Object.values(x))yield* walk(v);}}
const records=[];
mkdirSync(join(root,'runtime/source-transport'),{recursive:true});
for(const modality of ['box','diamond'])for(const viaIR of [false,true]){
 const source=join(root,'sources',`identity.${modality}.sol`);
 const out=join(root,'runtime/source-transport',`${modality}.${viaIR}.trimmed.json`);
 const args=['--solkey','/workspace/.setup/solkey','--soljson','/workspace/.setup/soljson','--source',source,'--out',out,'--no-wrapper'];
 if(viaIR)args.push('--via-ir');
 const r=compileFixture({args,quiet:true});
 assert.equal(r.sourceHash,sha(readFileSync(source)));
 assert.equal(r.compiler.sha256,'c8649f8d57f81b3244c7d2dd662efc0620d1ae296f623b347a2c616a6cfd11d8');
 const d=[...walk(r.rawAst)].find(n=>n.nodeType==='VariableDeclaration'&&n.name==='m');
 const allocation=[...walk(r.rawAst)].find(n=>n.nodeType==='FunctionCall'&&n.expression?.nodeType==='NewExpression');
 assert.equal(d.typeDescriptions.typeIdentifier,'t_array$_t_int256_$dyn_memory_ptr');
 assert.equal(allocation.tryCall,false);
 const trimmed=[...walk(r.primaryAst)].find(n=>n.nodeType==='VariableDeclaration'&&n.name==='m');
 records.push({source,sourceSha256:r.sourceHash,modality,viaIR,compiler:r.compiler,api:'compileFixture.rawAst/rawAsts',rawAstSha256:sha(JSON.stringify(r.rawAst)),trimmedHasRequiredIdentifier:!!trimmed?.typeDescriptions?.typeIdentifier,normalization:'Restore signed builtin referencedDeclaration IDs using existing compiler transport convention. No verifier called.'});
}
writeFileSync(join(root,'evidence/source-transport-records.json'),JSON.stringify(records,null,2)+'\n');
console.log('PASS existing compileFixture source transport: four fresh Identity compilations retain required full metadata in rawAst/rawAsts; no verifier invoked');
