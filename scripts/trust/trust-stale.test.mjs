// Regression: changing only an implemented_by target on the same source line
// must change the audited environment. lake env lean alone would reuse the old
// object and falsely retain the old twin's link evidence.
import {test} from 'node:test';
import assert from 'node:assert/strict';
import {mkdtempSync,mkdirSync,writeFileSync,readFileSync,rmSync} from 'node:fs';
import {tmpdir} from 'node:os';
import {join} from 'node:path';
import {extract} from './trust-closure.mjs';
test('audit rebuilds a same-line compiled twin change', {timeout:120000},()=>{
 const original=process.cwd(), dir=mkdtempSync(join(tmpdir(),'trust-stale-'));
 const toolchain=readFileSync('lean-toolchain','utf8');
 try {
  mkdirSync(join(dir,'Solidity'));
  writeFileSync(join(dir,'lakefile.toml'),'name = "trust-control"\n[[lean_lib]]\nname = "Solidity"\n');
  writeFileSync(join(dir,'lean-toolchain'),toolchain);
  const source=twin=>`namespace Solidity.Control\ndef good (n : Nat) := n\ndef bad (n : Nat) := n + 1\n@[implemented_by ${twin}] def logical (n : Nat) := n\nend Solidity.Control\n`;
  writeFileSync(join(dir,'Solidity/Control.lean'),source('good'));
  writeFileSync(join(dir,'audit.lean'),`import Solidity.Control
import Lean
open Lean Elab Command
run_elab do
  let some twin := Lean.Compiler.getImplementedBy? (← getEnv) \`\`Solidity.Control.logical
    | throwError "missing fixture attribute"
  liftM <| IO.println <| "TRUST_FIXTURE_JSON=" ++ (toJson twin.toString).compress
`);
  process.chdir(dir);
  assert.equal(extract('audit.lean','TRUST_FIXTURE_JSON='),'Solidity.Control.good');
  writeFileSync('Solidity/Control.lean',source('bad'));
  assert.equal(extract('audit.lean','TRUST_FIXTURE_JSON='),'Solidity.Control.bad');
 } finally {process.chdir(original);rmSync(dir,{recursive:true,force:true});}
});
