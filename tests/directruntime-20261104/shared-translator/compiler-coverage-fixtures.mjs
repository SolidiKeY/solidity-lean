import {retainCompilerMetadata} from './retained-metadata.mjs';
import {compileFixture} from '../../../scripts/solc-ast.mjs';
import {readFileSync,writeFileSync} from 'node:fs';
const owned='tests/directruntime-20261104/shared-translator';
const bulk=owned+'/artifacts/h68-bulk';
const base=['--solkey','/workspace/.setup/solkey','--soljson','/workspace/.setup/soljson','--no-wrapper'];
const yul=compileFixture({args:[...base,'--source',owned+'/YulKinds.sol','--out',bulk+'/YulKinds.ast.json']});
writeFileSync(bulk+'/YulKinds.ast.json',JSON.stringify(retainCompilerMetadata(yul).fixture,null,2)+'\n');
let rejected=false;
try {
  compileFixture({args:[...base,'--source',owned+'/LegacyThrow.sol','--out',owned+'/artifacts/LegacyThrow-unexpected.ast.json']});
} catch(error) {
  const diagnostics=error.diagnostics?.filter(d=>d.severity==='error');
  if(!diagnostics?.length)throw error;
  const source=readFileSync(owned+'/LegacyThrow.sol','utf8');
  if(!diagnostics.some(d=>d.sourceLocation && source.slice(d.sourceLocation.start,d.sourceLocation.end).includes('throw')))
    throw new Error('Compiler failure did not identify the legacy throw construct');
  writeFileSync(owned+'/artifacts/evidence/legacy-throw-rejection.json',JSON.stringify({
    compiler:'0.8.34+commit.80d5c536.Emscripten.clang',diagnostics,
    boundary:'External pinned-compiler rejection; no accepted modern Throw AST or source execution proof.'},null,2)+'\n');
  rejected=true;
}
if(!rejected)throw new Error('Modern compiler unexpectedly accepted throw');
console.log('Owned Yul source fixture generated; legacy throw rejected by pinned compiler.');
