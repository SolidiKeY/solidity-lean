/** Guards H90 narrow-local admission and overflow/wrapping/tuple regressions. */
import {compileFixture} from '../../../scripts/solc-ast.mjs';
import {retainCompilerMetadata} from './retained-metadata.mjs';
import {readFileSync,writeFileSync,mkdirSync} from 'node:fs';
import {createHash} from 'node:crypto';
const owned='tests/directruntime-20261104/shared-translator';
const out=owned+'/artifacts/h90';mkdirSync(out,{recursive:true});
const result=compileFixture({args:['--solkey','/workspace/.setup/solkey','--compiler-file','/workspace/.setup/soljson/soljson-v0.8.34+commit.80d5c536.js','--compiler-sha256','c8649f8d57f81b3244c7d2dd662efc0620d1ae296f623b347a2c616a6cfd11d8','--source',owned+'/NarrowLocalRuntime.sol','--out',out+'/NarrowLocalRuntime.normalized.json','--no-wrapper'],quiet:true});
const {fixture,fields}=retainCompilerMetadata(result);
const path=out+'/NarrowLocalRuntime.ast.json';writeFileSync(path,JSON.stringify(fixture,null,2)+'\n');
const receipt={regression:'H90 narrow-local width/overflow/wrapping/signed/tuple',compiler:result.compiler,sourceSha256:result.sourceHash,fixture:path,fixtureSha256:createHash('sha256').update(readFileSync(path)).digest('hex'),fieldsRetained:fields,boundary:'External compiler provenance; no Lean or semantic proof.'};
writeFileSync(out+'/narrow-local-compilation.json',JSON.stringify(receipt,null,2)+'\n');console.log(JSON.stringify(receipt));
