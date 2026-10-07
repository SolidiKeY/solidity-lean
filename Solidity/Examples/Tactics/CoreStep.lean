import Solidity.Calculus.Core.Step
import Solidity.Calculus.Core.Quote
import Solidity.Calculus.Core.Print
import Solidity.Calculus.Close

/-!
# Every statement's rule, on scoped formulas

`Calculus/Core/Step.lean`'s `Stmt.step` against `Completeness.lean`'s, arm
by arm: each program below is read into the scoped syntax
(`Prog.resolve`), run to its end by `Core.symex`, and its erasure compared
with what today's `symex` leaves of the same formula, each branch's cover
goal dropped (the scoped calculus keeps it apart, `Premise.cover`).  So
each premise erases to the one today's rule leaves, with the same fresh names.  The result is also
quoted and added as a theorem `Core.symex n φ = ψ` by `Eq.refl`, so the
kernel evaluates every arm too (a call's `Prog.wk`, a loop's frame).

`Examples/Tactics/CoreSymex.lean` prints three results; here a program only
has to agree.  A loop body's own locals are left out of the invariant
rule's `{anon(…)}` by the scoped frame (`Calculus/Core/Blocks.lean`), so the
loops below declare none.
-/

namespace Solidity.Examples.Tactics.CoreStep

open Solidity Lean Meta

/-- Today's formula with each branch's cover goal dropped. -/
private partial def dropCover {C : Contract} (c : Expr) : Solidity.Fml C → Solidity.Fml C
  | .and (.imp a x) (.and (.imp a' y) z) =>
    let q := Solidity.Fml.quote c
    if q z == q (Premise.coverFml .box a a') || q z == q (Premise.coverFml .diamond a a') then
      .and (.imp a (dropCover c x)) (.imp a' (dropCover c y))
    else .and (.imp a (dropCover c x)) (.and (.imp a' (dropCover c y)) (dropCover c z))
  | .and a b => .and (dropCover c a) (dropCover c b)
  | .imp a b => .imp a (dropCover c b)
  | .upd m U φ => .upd m U (dropCover c φ)
  | .not φ => .not (dropCover c φ)
  | .havoc φ => .havoc (dropCover c φ)
  | .all x p φ => .all x p (dropCover c φ)
  | .anon xs φ => .anon xs (dropCover c φ)
  | φ => φ

/-- The fuel: enough for every program below. -/
private def fuel : Nat := 2000

/-- Run `Core.symex` on the program of `φ` (a modality) read into the
scoped syntax, check that its erasure is today's result, and add
`name : Core.symex fuel φ' = ψ`, checked by the kernel. -/
private def agree (c : Expr) {C : Contract} (name : Lean.Name) (φ : Solidity.Fml C) :
    MetaM Unit := do
  let .modal m P _ := φ | throwError "not a modality"
  let .ok ⟨_, Pc⟩ := Core.Prog.resolve (C := C) [] P | throwError "the program does not resolve"
  let φc : Core.Fml C [] := .modal m Pc .nil .tt
  let ψ := Core.symex fuel φc
  let today := dropCover c (symex fuel (.modal m P .tt))
  unless Solidity.Fml.quote c (ψ.erase []) == Solidity.Fml.quote c today do
    throwError "the erasure is not today's result:\n{← Core.legacyShow c (ψ.erase [])}\n\
      today:\n{← Core.legacyShow c today}"
  let lhs := mkAppN (mkConst ``Core.symex) #[c, Core.Quote.qCtxRaw [], toExpr fuel, Core.Fml.quote c φc]
  let rhs := Core.Fml.quote c ψ
  addDecl (.thmDecl { name, levelParams := [], type := ← mkEq lhs rhs, value := ← mkEqRefl rhs })

/-! ## Storage: reads, writes, copies, deletes -/

section Standard

local instance : InContract := ⟨StandardExample⟩

def se : Expr := mkConst ``StandardExample

/-- `storageIndexReadMappingFind`, `storageIndexRead_unfold_rightSndIndex`,
`storageIndexRead_unfold_rightFst`, `storageLengthRead`,
`storageLengthRead_unfold_rightFst`. -/
private def readsφ : Solidity.Fml StandardExample :=
  dl!{ [ uint x = balances[3]; uint y = balances[x + 1]; uint z = people[x].age;
         uint w = people[total + 1].account.balance; uint l = values.length;
         uint n = matrix[x].length; ] true }

run_meta agree se `Solidity.Examples.Tactics.CoreStep.reads readsφ

/-- `storageIndexWriteMappingSave`, `indexWriteValueRhsCapture`,
`storageIndexWriteCaptureAllNonSimpleIndex`,
`storageIndexWriteCaptureAllComplexRecv`, `storageFieldWrite_unfold_leftFst`. -/
private def writesφ : Solidity.Fml StandardExample :=
  dl!{ [ balances[2] = 5; balances[2] = total + 1; balances[total + 1] = total;
         people[total].age = 3; values[total] = alice.age; matrix[total][1] = 4; ] true }

run_meta agree se `Solidity.Examples.Tactics.CoreStep.writes writesφ

/-- `storageRootWriteCopySource`, `storageIndexReadMappingStoreRoot`,
`storageFieldWriteCopySource`, `storageFieldRead_unfold_rightSndResult`,
`storageIndexWriteMappingCopySource`, `storageFieldWriteStorageRef_unfold_leftFst`,
`storageIndexWriteStorageRefCaptureAllNonSimpleIndex`. -/
private def copiesφ : Solidity.Fml StandardExample :=
  dl!{ [ alice = bob; alice = folks[1]; alice.account = bob.account;
         folks[1].account = people[2].account; folks[1] = alice; people[1].account = bob.account;
         folks[total + 1] = bob; ] true }

run_meta agree se `Solidity.Examples.Tactics.CoreStep.copies copiesφ

/-- `storageRootDelete`, `storageFieldDelete`, `storageIndexDelete`,
`storageIndexDeleteNonSimpleIndexCapture`, `storageFieldDelete_unfold_leftFst`,
`storageIndexDelete_unfold_leftFst`. -/
private def deletesφ : Solidity.Fml StandardExample :=
  dl!{ [ delete alice; delete alice.age; delete balances[2]; delete balances[total + 1];
         delete people[1].account; delete matrix[1][2]; ] true }

run_meta agree se `Solidity.Examples.Tactics.CoreStep.deletes deletesφ

/-- `storageFieldReadBindLocalRoot`, `storageIndexReadMappingBindLocalRoot`,
`storageLocalRootPushBind`, `storageLocalRootPush_unfold_leftFstReceiver`. -/
private def aliasesφ : Solidity.Fml StandardExample :=
  dl!{ [ Account storage a = alice.account; Person storage p = folks[2];
         Person storage q = people.push(); p = people[1]; a = folks[3].account; ] true }

run_meta agree se `Solidity.Examples.Tactics.CoreStep.aliases aliasesφ

/-! ## Operators, the conditional, `&&` and `||` -/

/-- `ternaryToIf`, `ternaryCaptureCond` into a local, a state variable and
an entry; `logicalAndShortCircuitRhs`, `logicalOrShortCircuitRhs`. -/
private def conditionalsφ : Solidity.Fml StandardExample :=
  dl!{ [ uint x = total > 1 ? 2 : 3; bool b = true; uint y = b ? x : 1; total = b ? 1 : 2;
         balances[1] = total > 2 ? 1 : 0; bool c = b && flags[2]; bool d = b || total > 3;
         bool e = flags[1] && flags[2]; ] true }

run_meta agree se `Solidity.Examples.Tactics.CoreStep.conditionals conditionalsφ

/-- Compound assignments and `++`/`--`, at a local, a state variable, a
member, an entry, with a source and a receiver to unfold. -/
private def compoundφ : Solidity.Fml StandardExample :=
  dl!{ [ uint x = 1; x += 2; total += x; alice.age -= 1; balances[2] *= 3;
         people[total].age += 1; total += x + 1; x++; total++; people[1].age++;
         uint y = x++; uint z = ++total; uint w = alice.age++; ] true }

run_meta agree se `Solidity.Examples.Tactics.CoreStep.compound compoundφ

/-! ## Arrays and payments -/

/-- `storagePushValueSave`, `storagePushValue_unfold_rightSndArgument`,
`storagePushLengthSave`, `storagePushLengthSaveReferenceElement`,
`storagePushValueCopySource`, `storagePushValue_unfold_leftFstReceiver`,
`storagePopSave`, `storagePop_unfold_leftFstReceiver`. -/
private def arraysφ : Solidity.Fml StandardExample :=
  dl!{ [ values.push(3); values.push(total + 1); values.push(); people.push();
         persons.push(alice); matrix[total].push(2); values.pop(); matrix[total].pop(); ] true }

run_meta agree se `Solidity.Examples.Tactics.CoreStep.arrays arraysφ

/-- `transferNoCallbackBox`, `transfer_unfold_rightSndArgument`,
`transfer_unfold_leftFstReceiver`, `sendNoCallbackBox`,
`send_unfold_rightSndArgument`. -/
private def paymentsφ : Solidity.Fml StandardExample :=
  dl!{ [ uint to = 9; to.transfer(5); to.transfer(total + 1); owner.transfer(2);
         bool ok; ok = to.send(3); ok = to.send(total); ] true }

run_meta agree se `Solidity.Examples.Tactics.CoreStep.payments paymentsφ

/-- Under the diamond: `transferDiamond`, `sendNoCallbackDiamond`. -/
private def paymentsDiamondφ : Solidity.Fml StandardExample :=
  dl!{ ⟨ uint to = 9; bool ok; ok = to.send(3); to.transfer(5); ⟩ true }

run_meta agree se `Solidity.Examples.Tactics.CoreStep.paymentsDiamond paymentsDiamondφ

/-! ## Memory -/

/-- The memory rules: declarations, rebinding, reads, writes, copies both
ways, deletes, fresh arrays. -/
private def memoryφ : Solidity.Fml StandardExample :=
  dl!{ [ Person memory m = alice; Person memory n; m.age = 3; uint x = m.age;
         m.account.balance = 2; uint y = m.account.balance; Account memory a = m.account;
         m.account = a; n = m; n = folks[x]; alice = m; folks[2] = n; people[x].account = a;
         delete m.age; delete m.account; delete m.account.balance; delete n;
         m.age = x + 1; ] true }

run_meta agree se `Solidity.Examples.Tactics.CoreStep.memory memoryφ

end Standard

/-! ## Loops -/

section Loops

local instance : InContract := ⟨StandardExample⟩

/-- `whileUnwind` then `loopExit`. -/
private def unwindφ : Solidity.Fml StandardExample :=
  dl!{ ⟨ uint i = 0;
         /// @custom:key unwind 2
         while (i < 3) { i = i + 1; total = i; }; ⟩ true }

run_meta agree se `Solidity.Examples.Tactics.CoreStep.unwind unwindφ

/-- `whileInvariantBox`: a body writing a local and storage. -/
private def invBoxφ : Solidity.Fml StandardExample :=
  dl!{ [ uint i = 0;
         /// @custom:key invariant i <= 3
         while (i < 3) { i = i + 1; total = i; }; ] true }

run_meta agree se `Solidity.Examples.Tactics.CoreStep.invBox invBoxφ

/-- `whileInvariantDiamond`. -/
private def invDiamondφ : Solidity.Fml StandardExample :=
  dl!{ ⟨ uint i = 0;
         /// @custom:key invariant i <= 3
         /// @custom:key decreases 3 - i
         while (i < 3) { i = i + 1; }; ⟩ true }

run_meta agree se `Solidity.Examples.Tactics.CoreStep.invDiamond invDiamondφ

/-- `whileClose`: the body pushes, so it has no frame. -/
private def invCloseφ : Solidity.Fml StandardExample :=
  dl!{ [ uint i = 0;
         /// @custom:key invariant i <= 3
         while (i < 3) { values.push(i); i = i + 1; }; ] true }

run_meta agree se `Solidity.Examples.Tactics.CoreStep.invClose invCloseφ

/-- `whileNoVariantDiamond`: a framed body under the diamond, with no
`decreases`. -/
private def invNoVariantφ : Solidity.Fml StandardExample :=
  dl!{ ⟨ uint i = 0;
         /// @custom:key invariant i <= 3
         while (i < 3) { i = i + 1; }; ⟩ true }

run_meta agree se `Solidity.Examples.Tactics.CoreStep.invNoVariant invNoVariantφ

end Loops

/-! ## Memory arrays, arrays of mapping-holding structs -/

section Suite

local instance : InContract := ⟨TestSuite⟩

private def ts : Expr := mkConst ``TestSuite

/-- The memory array rules: `memoryIndexReadArrayValue`,
`memoryIndexRead_unfold_rightSndIndex`, `memoryIndexRead_unfold_rightFst`,
`memoryLengthRead`, `memoryLengthRead_unfold_rightFst`,
`memoryIndexWriteCaptureAllComplexRecv`, `…NonSimpleIndex`,
`memoryIndexWriteMemRefCaptureAllComplexRecv`, `…NonSimpleIndex`, the
index deletes, `memoryIndexOpAssign…`, `memoryIndexArrayIncrement`,
`memoryFieldOpAssign…` and their `…UnfoldLeftFst`. -/
private def memoryArraysφ : Solidity.Fml TestSuite :=
  dl!{ [ uint i = 1; uint x = 2; Basket memory m = basketA;
         m.items[i] = x + 1; uint y = m.items[i + 1]; m.items[x] += 2; m.items[1]++;
         delete m.items[i + 1]; uint l = m.items.length; m.items[i + 1] = x;
         uint[] memory xs = m.items; uint z = xs[i]; xs[i + 1] = 4; xs[i] = y; xs[i]++;
         xs[x] -= 1; delete xs[i]; delete xs[i + 1]; uint n = xs.length;
         TokenBucket memory b = bucket; Token memory t = tok; b.tokens[i] = t;
         Token[] memory ks = b.tokens; ks[i + 1] = t; b.tokens[i].value = 3;
         uint v = b.tokens[i + 1].value; t.value += 2; b.tokens[i].value += 1;
         b.tokens[i].value++; ] true }

run_meta agree ts `Solidity.Examples.Tactics.CoreStep.memoryArrays memoryArraysφ

/-- Arrays whose elements hold a mapping: `storagePopSaveMappingElement`,
`storageLocalRootPushBindMappingElement`,
`storageIndexReadArrayBindLocalRootMappingElement`; a reference written
under a complex receiver (`storageIndexWriteStorageRefCaptureAllComplexRecv`)
and from memory (`memoryToStorageIndexCaptureAllComplexRecv`,
`…NonSimpleIndex`). -/
private def suiteArraysφ : Solidity.Fml TestSuite :=
  dl!{ [ uint i = 1; uint x = 2; LedgerUse storage u = ledgerUses.push(); ledgerUses.pop();
         LedgerUse storage w = ledgerUses[i]; w = ledgerUses[x]; u = ledgerUses.push();
         buckets[x].tokens[i + 1] = tok;
         Person memory m = alice; persons[i + 1] = m; Token memory t = tok;
         buckets[x].tokens[i] = t; ] true }

run_meta agree ts `Solidity.Examples.Tactics.CoreStep.suiteArrays suiteArraysφ

end Suite

/-! ## Calls -/

section Calls

local instance : InContract := ⟨CallsExample⟩

private def ce : Expr := mkConst ``CallsExample

/-- `internalCallExpand` with a result, a nested call, `functionCallArgCapture`,
a call with no result. -/
private def callsφ : Solidity.Fml CallsExample :=
  dl!{ [ uint y = addOne(4); uint z = addTwo(y); uint w = addOne(y + 1); credit(y, 5); bump();
         uint v = larger(z, w + 1); ] true }

run_meta agree ce `Solidity.Examples.Tactics.CoreStep.calls callsφ

end Calls

/-! ## Calls that leave their returns, fresh arrays -/

/-- Functions returning a pair and a memory object, and a basket. -/
def Rets : Contract := contract!{
  uint total; Basket basket;
  function pair(uint x) returns (uint lo, uint hi) { return (x, x + 1); }
  function mk(uint x) returns (Person memory p) { p.age = x; }
}

section Rets

local instance : InContract := ⟨Rets⟩

private def re : Expr := mkConst ``Rets

/-- `functionBodyExpand` (a tuple's call leaves its return variables), a
memory return, each with an argument captured first; `newArrayCapture`
into memory and into storage, `memoryArrayFreshAlloc`. -/
private def retsφ : Solidity.Fml Rets :=
  dl!{ [ uint a; uint b; (a, b) = pair(3); (a, b) = pair(a + 1); Person memory m = mk(2);
         Person memory n = mk(total + 1); uint y = n.age; Basket memory k; k.items = new uint[](3);
         basket.items = new uint[](a); uint[] memory xs = new uint[](2); ] true }

run_meta agree re `Solidity.Examples.Tactics.CoreStep.rets retsφ

end Rets

/-! ## `try` -/

/-- A contract that pings another. -/
def Pinger : Contract := contract!{ uint pings; uint last; }

section Try

local instance : InContract := ⟨Pinger⟩

private def pe : Expr := mkConst ``Pinger

/-- `tryCallNoCallbackBox`. -/
private def tryBoxφ : Solidity.Fml Pinger :=
  dl!{ [ try I(7).get() returns (uint v) { last = v; } catch Panic(uint c) { last = c; }
         catch { last = 0; }; pings = 1; ] true }

run_meta agree pe `Solidity.Examples.Tactics.CoreStep.tryBox tryBoxφ

/-- `tryCallDiamond`. -/
private def tryDiamondφ : Solidity.Fml Pinger :=
  dl!{ ⟨ try I(7).get() returns (uint v) { last = v; } catch { last = 0; }; ⟩ true }

run_meta agree pe `Solidity.Examples.Tactics.CoreStep.tryDiamond tryDiamondφ

end Try

end Solidity.Examples.Tactics.CoreStep
