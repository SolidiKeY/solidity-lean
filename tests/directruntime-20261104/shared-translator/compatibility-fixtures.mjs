import {compileFixture} from '../../../scripts/solc-ast.mjs';
import {retainCompilerMetadata} from './retained-metadata.mjs';
import {readFileSync,writeFileSync,mkdirSync} from 'node:fs';
import {createHash} from 'node:crypto';
const owned='tests/directruntime-20261104/shared-translator';
const sha=x=>createHash('sha256').update(x).digest('hex');
const bulk=owned+'/artifacts/h68-bulk';
const receipts=[];mkdirSync(bulk+'/evidence/h68/metadata',{recursive:true});
for(const name of ['ReaderFixtures','UnsupportedContract','YulKinds','ComposedReaders','ModalityControls']){
 const source=owned+'/'+name+'.sol',out=bulk+'/'+name+'.ast.json';
 const baselineFixture=owned+'/'+name+'.ast.json';const previous=readFileSync(baselineFixture);const old=JSON.parse(previous);
 const result=compileFixture({args:['--solkey','/workspace/.setup/solkey','--compiler-file','/workspace/.setup/soljson/soljson-v0.8.34+commit.80d5c536.js','--compiler-sha256','c8649f8d57f81b3244c7d2dd662efc0620d1ae296f623b347a2c616a6cfd11d8','--source',source,'--out',owned+'/artifacts/h68/'+name+'.normalized.json','--no-wrapper'],quiet:true});
 const {fixture,fields}=retainCompilerMetadata(result);
 const strip=x=>JSON.stringify(x,(k,v)=>k==='typeIdentifier'||k==='tryCall'?undefined:v);
 if(strip(old)!==strip(fixture))throw new Error(name+': changes beyond metadata retention');
 writeFileSync(out,JSON.stringify(fixture,null,2)+'\n');
 const rawAst=bulk+'/evidence/h68/metadata/'+name+'.raw.json';writeFileSync(rawAst,JSON.stringify(result.rawAst));
 const receipt={name,baselineFixture,compiler:result.compiler,source,sourceSha256:result.sourceHash,fixture:out,previousFixtureSha256:sha(previous),fixtureSha256:sha(readFileSync(out)),rawAst,rawAstSha256:sha(readFileSync(rawAst)),fieldsRetained:fields,normalizationAndAnnotationsUnchanged:true,fieldCountBasis:'Fields added to existing helper normalized output; not differences from a previously migrated fixture.'};
 receipts.push(receipt);
 if(name==='ModalityControls')writeFileSync(bulk+'/evidence/h68/modality-compilation.json',JSON.stringify(receipt,null,2)+'\n');
}
writeFileSync(bulk+'/evidence/h68/metadata-compilation.json',JSON.stringify({authority:'H68 option 1',fixtures:receipts,boundary:'External compiler and metadata-only fixture migration. No producer-owned code changed; no semantic or source-preservation theorem.'},null,2)+'\n');
console.log(JSON.stringify(receipts.map(({name,fieldsRetained,previousFixtureSha256,fixtureSha256})=>({name,fieldsRetained,previousFixtureSha256,fixtureSha256}))));
