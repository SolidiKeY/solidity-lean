/** Portable compiler locations for pinned source/reference regression tests.
 * Populate .lake/soljson/ with the exact filenames from COMPILERS, or set
 * SOLJSON_DIR. SOLC_REFERENCE selects the 0.8.38 reference file explicitly.
 * These are location overrides only: snapshot and compiler hashes still apply.
 */
import {readFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {dirname,join,resolve} from 'node:path';
import {fileURLToPath} from 'node:url';
import {COMPILERS} from './solc-unit.mjs';
import {verifySnapshot} from './solkey-migration.mjs';

const root=resolve(dirname(fileURLToPath(import.meta.url)),'..');
const compilerDirectory=()=>resolve(process.env.SOLJSON_DIR ?? join(root,'.lake/soljson'));

function checkedCompiler(path,pin) {
  let bytes;
  try { bytes=readFileSync(path); }
  catch(e) { throw new Error(`Missing pinned compiler ${path}; populate .lake/soljson or set SOLJSON_DIR (SOLC_REFERENCE for 0.8.38).`,{cause:e}); }
  if(createHash('sha256').update(bytes).digest('hex')!==pin.sha256)
    throw new Error(`Pinned compiler SHA-256 mismatch: ${path}`);
  return path;
}

export function referenceCompiler() {
  const pin=COMPILERS.find(p=>p.version==='0.8.38+commit.1835d247.Emscripten.clang');
  return checkedCompiler(resolve(process.env.SOLC_REFERENCE ?? join(compilerDirectory(),pin.file)),pin);
}

/** Test the repository's frozen SolKey snapshot without a sibling checkout. */
export function solkeyTestOptions() {
  const solkey=join(root,'tests/migration/solkey');
  verifySnapshot(solkey);
  const gradle=readFileSync(join(solkey,'keyext.solidity.core/build.gradle'),'utf8');
  const file=gradle.match(/ext\.soljsonFile\s*=\s*"([^"]+)"/)?.[1];
  const sha256=gradle.match(/ext\.soljsonSha256\s*=\s*"([0-9a-f]{64})"/)?.[1];
  const pin=COMPILERS.find(p=>p.file===file && p.sha256===sha256);
  if(!pin) throw new Error('Unsupported compiler pin in frozen SolKey snapshot');
  const soljson=compilerDirectory();
  checkedCompiler(join(soljson,pin.file),pin);
  return {solkey,soljson};
}
