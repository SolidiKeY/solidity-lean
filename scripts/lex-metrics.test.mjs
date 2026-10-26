import {test} from 'node:test';
import assert from 'node:assert/strict';
import {execFileSync} from 'node:child_process';
import {mkdtempSync,readFileSync,writeFileSync,rmSync} from 'node:fs';
import {tmpdir} from 'node:os';
import {join,resolve} from 'node:path';
import {runSolidityTests,testsPassed} from './test-solidity.mjs';

const source = 'tests/solc/LexMetrics.sol';

test('tuple annotations preserve ordinary safety proofs and do not claim automatic termination', () => {
  const report = runSolidityTests([source],{build:false,contract:'LexMetrics'});
  assert.deepEqual(report.errors,[]);
  const rows = new Map(report.results.map(row => [row.function,row]));
  for (const name of ['resetInner','triple','forScope','doWhileLoop','breakLoop','continueLoop','renamed','nested','earlyReturn'])
    assert.equal(rows.get(name)?.status,'proved',`${name}: ${rows.get(name)?.reason}`);
  assert.equal(rows.get('shadowed')?.status,'unsupported');
  assert.match(rows.get('shadowed')?.reason,/already declared/);
  assert.equal(rows.get('diamondStillOpen')?.status,'pending');
  assert.equal(rows.get('callback')?.status,'proved');
  assert.equal(testsPassed(report),false);
});

test('every malformed or effectful tuple component remains an explicit import gap', () => {
  const report = runSolidityTests([source],{build:false,contract:'InvalidLexMetrics'});
  const names = ['wrongType','badSecond','badThird','unknown','nestedTuple','effect','cast','empty','trailing','duplicate','noInvariant','conflicting'];
  for (const name of names) {
    const row = report.results.find(row => row.function === name);
    assert.ok(row,`${name}: missing result`);
    assert.ok(['error','excluded','unsupported'].includes(row.status),`${name}: ${row.status}`);
    assert.ok(row.reason.length,name);
  }
  assert.equal(testsPassed(report),false);
});

test('solc-imported programs retain every tuple in order through loop lowering and quotation', () => {
  const root = mkdtempSync(join(tmpdir(),'solidity-lex-shape-'));
  try {
    const fixture = join(root,'source.ast.json');
    execFileSync(process.execPath,['scripts/solc-ast.mjs','--source',resolve(source),'--out',fixture,'--no-wrapper'],{timeout:30000});
    let hash = 0xcbf29ce484222325n;
    for (const byte of readFileSync(fixture)) hash = BigInt.asUintN(64,(hash ^ BigInt(byte))*0x100000001b3n);
    const wrapper = join(root,'Shape.lean');
    writeFileSync(wrapper,`import Solidity.Frontend.Testing
open Solidity
solc_import "source.ast.json" hash 0x${hash.toString(16)} as Imported.LexMetrics testing

mutual
def tupleTextsP {C : Contract} : {Γ Δ : Ctx} → Prog C Γ Δ → List (List String)
  | _, _, .nil => []
  | _, _, .cons s rest => tupleTextsS s ++ tupleTextsP rest
def tupleTextsS {C : Contract} : {Γ Δ : Ctx} → Stmt C Γ Δ → List (List String)
  | _, _, .loop a _ body =>
    (match a with
      | .invLex _ metrics _ _ => [metrics.toList.map (fun value => value.toStr [] true)]
      | _ => []) ++ tupleTextsP body
  | _, _, .block body => tupleTextsP body
  | _, _, .ite _ left right => tupleTextsP left ++ tupleTextsP right
  | _, _, _ => []
end

example : (tupleTextsP Imported.LexMetrics.resetInner).map List.length = [2] := by decide +kernel
example : (tupleTextsP Imported.LexMetrics.triple).map List.length = [3] := by decide +kernel
example : (tupleTextsP Imported.LexMetrics.triple).head!.drop 1 = ["0", "0"] := by decide +kernel
example : (tupleTextsP Imported.LexMetrics.forScope).map List.length = [2] := by decide +kernel
example : (tupleTextsP Imported.LexMetrics.doWhileLoop).map List.length = [2] := by decide +kernel
example : (tupleTextsP Imported.LexMetrics.breakLoop).map List.length = [2] := by decide +kernel
example : (tupleTextsP Imported.LexMetrics.continueLoop).map List.length = [2] := by decide +kernel
example : (tupleTextsP Imported.LexMetrics.renamed).map List.length = [2] := by decide +kernel
example : (tupleTextsP Imported.LexMetrics.nested).map List.length = [2, 2] := by decide +kernel
example : (tupleTextsP Imported.LexMetrics.earlyReturn).map List.length = [2] := by decide +kernel
example : (tupleTextsP Imported.LexMetrics.callback).map List.length = [2] := by decide +kernel

solc_scoped_problems Imported.LexMetrics decl
#solkey_test Imported.LexMetrics only "callback" to ${JSON.stringify(join(root,'callback.json'))}
example : ValidT (.noCallback invariant[Imported.LexMetrics]) Imported.LexMetrics.callback.problem :=
  Imported.LexMetrics.callback.tested
`);
    try {
      execFileSync('lake',['--quiet','--no-build','lean',wrapper,'--','--tstack=131072'],{timeout:60000,stdio:'pipe',maxBuffer:4*1024*1024});
    } catch (error) {
      throw new Error(`Lean tuple-shape check failed:\n${error.stdout?.toString().slice(-16000) || error.message.slice(-16000)}`);
    }
  } finally {
    rmSync(root,{recursive:true,force:true});
  }
});
