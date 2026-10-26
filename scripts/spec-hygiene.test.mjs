import {test} from 'node:test';
import assert from 'node:assert/strict';
import {execFileSync} from 'node:child_process';
import {mkdtempSync,writeFileSync,rmSync} from 'node:fs';
import {tmpdir} from 'node:os';
import {join} from 'node:path';
import {runSolidityTests,testsPassed} from './test-solidity.mjs';

const source = 'tests/solc/SpecHygiene.sol';

test('existing specification quantifiers preserve ordinary lexical shadowing and hidden references', () => {
  const report = runSolidityTests([source],{build:false,contract:'SpecHygiene'});
  const rows = new Map(report.results.map(row => [row.function,row]));
  assert.equal(report.results.length,rows.size);
  const good = ['stateNameShadow','arrayNameShadow','parameterShadow','resultReference',
    'namedReturnShadow','snapshotReference','nestedShadow'];
  const reserved = ['captureResult','captureNamedReturn','captureOld','captureOldNet',
    'captureNestedResult','reservedFalseBody','reservedVacuousBody'];
  const paths = ['arrayLength','arrayFalseGuard','arrayEmptyGuard','arrayIndex','mappingIndex',
    'mappingEmptyGuard','structField','structFalseGuard','memoryLength','memoryFalseGuard','memoryEmptyGuard'];
  assert.equal(rows.size,good.length + reserved.length + paths.length + 1);
  for (const name of good)
    assert.equal(rows.get(name)?.status,'proved',`${name}: ${JSON.stringify(rows.get(name))}`);
  assert.equal(rows.get('falseResult')?.status,'pending');
  for (const name of reserved) {
    const row = rows.get(name);
    assert.equal(row?.status,'error',`${name}: ${JSON.stringify(row)}`);
    assert.match(row.reason,/reserved specification binder name/);
  }
  for (const name of paths) {
    const row = rows.get(name);
    assert.equal(row?.status,'error',`${name}: ${JSON.stringify(row)}`);
    assert.match(row.reason,/primitive local.*(?:reference|storage) path/);
  }
  assert.ok(report.errors.length > 0,'invalid clauses must retain elaboration diagnostics');
  assert.equal(testsPassed(report),false);
});

test('the existing spec compiler rejects capture before simplifying vacuous guards', () => {
  const directory = mkdtempSync(join(tmpdir(),'solidity-spec-hygiene-'));
  const file = join(directory,'Check.lean');
  try {
    writeFileSync(file,String.raw`import Solidity.Frontend.Testing
open Solidity
def Model : Contract := contract!{
  uint value;
  uint[] entries;
  mapping(uint => uint) table;
}
def context : SpecCtx Model :=
  {storage := .storage, ensures := true, locals := [], result := some .uint}
def compile (e : SpecExpr) : Except String (Fml Model []) := do
  let read ← e.fml Model context
  read []
#guard (compile (spec!(\forall uint entries; entries == entries))).isOk
#guard (compile (spec!(\forall uint entries; false -> entries.length == 0))).isOk == false
#guard (compile (spec!(\exists uint entries; false && entries[0] == 0))).isOk == false
#guard (compile (spec!(\forall uint table; table[0] == table[0]))).isOk == false
#guard (compile (spec!(\exists uint result; false))).isOk == false
#guard (compile (spec!(\forall uint result_first; true))).isOk == false
#guard (compile (spec!(\forall uint old; true))).isOk == false
#guard (compile (spec!(\exists uint oldNet; true))).isOk == false
#guard (compile (spec!(\forall uint x; \exists uint result; true))).isOk == false

def nested : Except String (Fml Model [.val .uint]) := do
  let read ← (spec!(\forall uint x; x == x)).fml Model
    {context with locals := [("x",.uint)]}
  read [(Var.ofName "x",.val .uint)]
#guard match nested with
  | .ok (.all _ _ (.eq (.pvV .here) (.pvV .here))) => true
  | _ => false

def resultRead : Except String (Fml Model [.val .uint]) := do
  let read ← (spec!(\forall uint x; \result == 2)).fml Model context
  read [(Var.ofName "result",.val .uint)]
#guard match resultRead with
  | .ok (.all _ _ (.eq (.pvV (.there .here)) _)) => true
  | _ => false
`);
    const result = execFileSync('lake',['--quiet','--no-build','lean',file,'--','--tstack=131072'],
      {timeout:120000,encoding:'utf8',maxBuffer:8*1024*1024});
    assert.equal(typeof result,'string');
  } finally { rmSync(directory,{recursive:true,force:true}); }
});
