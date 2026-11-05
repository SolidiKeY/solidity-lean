import {compileFixture} from '../../../scripts/solc-ast.mjs';
import {readFileSync,writeFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
const owned='tests/directruntime-20261104/shared-translator';
const sha=x=>createHash('sha256').update(x).digest('hex');
const result=compileFixture({args:['--solkey','/workspace/.setup/solkey','--soljson','/workspace/.setup/soljson','--source',owned+'/ComposedReaders.sol','--out',owned+'/artifacts/ComposedReaders.normalized.json','--no-wrapper'],quiet:true});
const metadata=new Map();
function walk(n,act){if(!n||typeof n!=='object')return;act(n);for(const v of Object.values(n))if(Array.isArray(v))v.forEach(x=>walk(x,act));else if(v&&typeof v==='object')walk(v,act);}
walk(result.rawAst,n=>{if(n.nodeType&&n.src){const key=n.nodeType+':'+n.src;const old=metadata.get(key);if(old&&JSON.stringify(old.typeDescriptions)!==JSON.stringify(n.typeDescriptions))throw new Error('ambiguous metadata source range');metadata.set(key,n);}});
const fixture=structuredClone(result.fixture);const added=[];
walk(fixture.ast,n=>{const raw=metadata.get(n.nodeType+':'+n.src);if(!raw)return;
 if(n.typeDescriptions&&typeof raw.typeDescriptions?.typeIdentifier==='string'){
  if(n.typeDescriptions.typeString!==raw.typeDescriptions.typeString)throw new Error('compiler type metadata mismatch');
  if(!('typeIdentifier'in n.typeDescriptions)){n.typeDescriptions.typeIdentifier=raw.typeDescriptions.typeIdentifier;added.push([n,'typeIdentifier']);}
 }
 if(typeof raw.tryCall==='boolean'&&!('tryCall'in n)){n.tryCall=raw.tryCall;added.push([n,'tryCall']);}
});
const retained=structuredClone(fixture.ast);
walk(retained,n=>{const canonical=metadata.get(n.nodeType+':'+n.src);if(!canonical)return;
 if(n.typeDescriptions)delete n.typeDescriptions.typeIdentifier;
 delete n.tryCall;
});
const original=structuredClone(result.annotationAst);
walk(original,n=>{if(n.typeDescriptions)delete n.typeDescriptions.typeIdentifier;delete n.tryCall;});
if(JSON.stringify(retained)!==JSON.stringify(original))throw new Error('metadata retention changed normalized syntax');
const out=owned+'/ComposedReaders.ast.json';writeFileSync(out,JSON.stringify(fixture,null,2)+'\n');
writeFileSync(owned+'/evidence/adoption-8495/composed-compilation.json',JSON.stringify({compiler:result.compiler,sourceSha256:result.sourceHash,rawAstSha256:sha(JSON.stringify(result.rawAst)),fixture:out,fixtureSha256:sha(readFileSync(out)),compilerMetadataFieldsRetainedBySourceRange:added.length,canonicalSyntaxAndBuiltinNormalizationUnchanged:true,boundary:'Test-only retention of typeIdentifier/tryCall metadata on existing normalized producer AST. Existing builtin-ID normalization and loopSpec extraction are retained; no new translation semantics/source proof.'},null,2)+'\n');
console.log('Pinned fixture generated through existing normalization; required metadata retained by source identity; normalized syntax/builtin IDs unchanged.');
