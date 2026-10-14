import Solidity.Calculus.Step
import Solidity.Calculus.Quote
import Solidity.Calculus.Print
import Solidity.Calculus.Close
import Solidity.Calculus.Notation

/-!
# Every statement's rule, on scoped formulas

`Calculus/Step.lean`'s `Stmt.step`, arm by arm: each program below is
read scoped by `dl!{ … }`, run to its end by
`symex`, quoted and added as a theorem `symex n φ = ψ` by
`Eq.refl`, so the kernel evaluates every arm (a call's `Prog.wk`, a loop's
frame).  Until W4 `calc-del` each result's erasure was also compared with
what today's strategy left (each branch's cover goal dropped, the same
fresh names); that strategy is deleted with today's rule table.

`Examples/Tactics/Symex.lean` prints three results; here a program only
has to agree.  A loop body's own locals are left out of the invariant
rule's `{anon(…)}` by the scoped frame (`Calculus/Blocks.lean`), so the
loops below declare none.
-/

namespace Solidity.Examples.Tactics.Step

open Solidity Lean Meta

/-- The fuel: enough for every program below. -/
private def fuel : Nat := 2000

/-- Run `symex` on `φ` (a modality) and add `name : symex fuel φ = ψ`,
checked by the kernel. -/
private def agree (c : Expr) {C : Contract} (name : Lean.Name) (φ : Fml C []) :
    MetaM Unit := do
  let ψ := symex fuel φ
  let lhs := mkAppN (mkConst ``symex) #[c, Quote.qCtxRaw [], toExpr fuel, Fml.quote c φ]
  let rhs := Fml.quote c ψ
  addDecl (.thmDecl { name, levelParams := [], type := ← mkEq lhs rhs, value := ← mkEqRefl rhs })

/-! ## Storage: reads, writes, copies, deletes -/

section Standard

local instance : InContract := ⟨StandardExample⟩

def se : Expr := mkConst ``StandardExample

/-- `storageIndexReadMappingFind`, `storageIndexRead_unfold_rightSndIndex`,
`storageIndexRead_unfold_rightFst`, `storageLengthRead`,
`storageLengthRead_unfold_rightFst`. -/
private def readsφ : Fml StandardExample [] :=
  dl!{ [ uint x = balances[3]; uint y = balances[x + 1]; uint z = people[x].age;
         uint w = people[total + 1].account.balance; uint l = values.length;
         uint n = matrix[x].length; ] true }

run_meta agree se `Solidity.Examples.Tactics.Step.reads readsφ

/-- `storageIndexWriteMappingSave`, `indexWriteValueRhsCapture`,
`storageIndexWriteCaptureAllNonSimpleIndex`,
`storageIndexWriteCaptureAllComplexRecv`, `storageFieldWrite_unfold_leftFst`. -/
private def writesφ : Fml StandardExample [] :=
  dl!{ [ balances[2] = 5; balances[2] = total + 1; balances[total + 1] = total;
         people[total].age = 3; values[total] = alice.age; matrix[total][1] = 4; ] true }

run_meta agree se `Solidity.Examples.Tactics.Step.writes writesφ

/-- `storageRootWriteCopySource`, `storageIndexReadMappingStoreRoot`,
`storageFieldWriteCopySource`, `storageFieldRead_unfold_rightSndResult`,
`storageIndexWriteMappingCopySource`, `storageFieldWriteStorageRef_unfold_leftFst`,
`storageIndexWriteStorageRefCaptureAllNonSimpleIndex`. -/
private def copiesφ : Fml StandardExample [] :=
  dl!{ [ alice = bob; alice = folks[1]; alice.account = bob.account;
         folks[1].account = people[2].account; folks[1] = alice; people[1].account = bob.account;
         folks[total + 1] = bob; ] true }

run_meta agree se `Solidity.Examples.Tactics.Step.copies copiesφ

/-- `storageRootDelete`, `storageFieldDelete`, `storageIndexDelete`,
`storageIndexDeleteNonSimpleIndexCapture`, `storageFieldDelete_unfold_leftFst`,
`storageIndexDelete_unfold_leftFst`. -/
private def deletesφ : Fml StandardExample [] :=
  dl!{ [ delete alice; delete alice.age; delete balances[2]; delete balances[total + 1];
         delete people[1].account; delete matrix[1][2]; ] true }

run_meta agree se `Solidity.Examples.Tactics.Step.deletes deletesφ

/-- `storageFieldReadBindLocalRoot`, `storageIndexReadMappingBindLocalRoot`,
`storageLocalRootPushBind`, `storageLocalRootPush_unfold_leftFstReceiver`. -/
private def aliasesφ : Fml StandardExample [] :=
  dl!{ [ Account storage a = alice.account; Person storage p = folks[2];
         Person storage q = people.push(); p = people[1]; a = folks[3].account; ] true }

run_meta agree se `Solidity.Examples.Tactics.Step.aliases aliasesφ

/-! ## Operators, the conditional, `&&` and `||` -/

/-- `ternaryToIf`, `ternaryCaptureCond` into a local, a state variable and
an entry; `logicalAndShortCircuitRhs`, `logicalOrShortCircuitRhs`. -/
private def conditionalsφ : Fml StandardExample [] :=
  dl!{ [ uint x = total > 1 ? 2 : 3; bool b = true; uint y = b ? x : 1; total = b ? 1 : 2;
         balances[1] = total > 2 ? 1 : 0; bool c = b && flags[2]; bool d = b || total > 3;
         bool e = flags[1] && flags[2]; ] true }

run_meta agree se `Solidity.Examples.Tactics.Step.conditionals conditionalsφ

/-- Compound assignments and `++`/`--`, at a local, a state variable, a
member, an entry, with a source and a receiver to unfold. -/
private def compoundφ : Fml StandardExample [] :=
  dl!{ [ uint x = 1; x += 2; total += x; alice.age -= 1; balances[2] *= 3;
         people[total].age += 1; total += x + 1; x++; total++; people[1].age++;
         uint y = x++; uint z = ++total; uint w = alice.age++; ] true }

run_meta agree se `Solidity.Examples.Tactics.Step.compound compoundφ

/-! ## Arrays and payments -/

/-- `storagePushValueSave`, `storagePushValue_unfold_rightSndArgument`,
`storagePushLengthSave`, `storagePushLengthSaveReferenceElement`,
`storagePushValueCopySource`, `storagePushValue_unfold_leftFstReceiver`,
`storagePopSave`, `storagePop_unfold_leftFstReceiver`, `storageLocalPrimitivePushBind`. -/
private def arraysφ : Fml StandardExample [] :=
  dl!{ [ values.push(3); values.push(total + 1); values.push(); people.push();
         persons.push(alice); matrix[total].push(2); values.pop(); matrix[total].pop();
         uint y; y = values.push(); ] true }

run_meta agree se `Solidity.Examples.Tactics.Step.arrays arraysφ

/-- `transferNoCallbackBox`, `transfer_unfold_rightSndArgument`,
`transfer_unfold_leftFstReceiver`, `sendNoCallbackBox`,
`send_unfold_rightSndArgument`. -/
private def paymentsφ : Fml StandardExample [] :=
  dl!{ [ uint to = 9; to.transfer(5); to.transfer(total + 1); owner.transfer(2);
         bool ok; ok = to.send(3); ok = to.send(total); ] true }

run_meta agree se `Solidity.Examples.Tactics.Step.payments paymentsφ

/-- Under the diamond: `transferDiamond`, `sendNoCallbackDiamond`. -/
private def paymentsDiamondφ : Fml StandardExample [] :=
  dl!{ ⟨ uint to = 9; bool ok; ok = to.send(3); to.transfer(5); ⟩ true }

run_meta agree se `Solidity.Examples.Tactics.Step.paymentsDiamond paymentsDiamondφ

/-! ## Memory -/

/-- The memory rules: declarations, rebinding, reads, writes, copies both
ways, deletes, fresh arrays. -/
private def memoryφ : Fml StandardExample [] :=
  dl!{ [ Person memory m = alice; Person memory n; m.age = 3; uint x = m.age;
         m.account.balance = 2; uint y = m.account.balance; Account memory a = m.account;
         m.account = a; n = m; n = folks[x]; alice = m; folks[2] = n; people[x].account = a;
         delete m.age; delete m.account; delete m.account.balance; delete n;
         m.age = x + 1; ] true }

run_meta agree se `Solidity.Examples.Tactics.Step.memory memoryφ

end Standard

/-! ## Loops -/

section Loops

local instance : InContract := ⟨StandardExample⟩

/-- `whileUnwind` then `loopExit`. -/
private def unwindφ : Fml StandardExample [] :=
  dl!{ ⟨ uint i = 0;
         /// @custom:key unwind 2
         while (i < 3) { i = i + 1; total = i; }; ⟩ true }

run_meta agree se `Solidity.Examples.Tactics.Step.unwind unwindφ

/-- `whileInvariantBox`: a body writing a local and storage. -/
private def invBoxφ : Fml StandardExample [] :=
  dl!{ [ uint i = 0;
         /// @custom:key invariant i <= 3
         while (i < 3) { i = i + 1; total = i; }; ] true }

run_meta agree se `Solidity.Examples.Tactics.Step.invBox invBoxφ

/-- `whileInvariantDiamond`. -/
private def invDiamondφ : Fml StandardExample [] :=
  dl!{ ⟨ uint i = 0;
         /// @custom:key invariant i <= 3
         /// @custom:key decreases 3 - i
         while (i < 3) { i = i + 1; }; ⟩ true }

run_meta agree se `Solidity.Examples.Tactics.Step.invDiamond invDiamondφ

/-- `whileClose`: the body pushes, so it has no frame. -/
private def invCloseφ : Fml StandardExample [] :=
  dl!{ [ uint i = 0;
         /// @custom:key invariant i <= 3
         while (i < 3) { values.push(i); i = i + 1; }; ] true }

run_meta agree se `Solidity.Examples.Tactics.Step.invClose invCloseφ

/-- `whileNoVariantDiamond`: a framed body under the diamond, with no
`decreases`. -/
private def invNoVariantφ : Fml StandardExample [] :=
  dl!{ ⟨ uint i = 0;
         /// @custom:key invariant i <= 3
         while (i < 3) { i = i + 1; }; ⟩ true }

run_meta agree se `Solidity.Examples.Tactics.Step.invNoVariant invNoVariantφ

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
private def memoryArraysφ : Fml TestSuite [] :=
  dl!{ [ uint i = 1; uint x = 2; Basket memory m = basketA;
         m.items[i] = x + 1; uint y = m.items[i + 1]; m.items[x] += 2; m.items[1]++;
         delete m.items[i + 1]; uint l = m.items.length; m.items[i + 1] = x;
         uint[] memory xs = m.items; uint z = xs[i]; xs[i + 1] = 4; xs[i] = y; xs[i]++;
         xs[x] -= 1; delete xs[i]; delete xs[i + 1]; uint n = xs.length;
         TokenBucket memory b = bucket; Token memory t = tok; b.tokens[i] = t;
         Token[] memory ks = b.tokens; ks[i + 1] = t; b.tokens[i].value = 3;
         uint v = b.tokens[i + 1].value; t.value += 2; b.tokens[i].value += 1;
         b.tokens[i].value++; ] true }

run_meta agree ts `Solidity.Examples.Tactics.Step.memoryArrays memoryArraysφ

/-- Arrays whose elements hold a mapping: `storagePopSaveMappingElement`,
`storageLocalRootPushBindMappingElement`,
`storageIndexReadArrayBindLocalRootMappingElement`; a reference written
under a complex receiver (`storageIndexWriteStorageRefCaptureAllComplexRecv`)
and from memory (`memoryToStorageIndexCaptureAllComplexRecv`,
`…NonSimpleIndex`). -/
private def suiteArraysφ : Fml TestSuite [] :=
  dl!{ [ uint i = 1; uint x = 2; LedgerUse storage u = ledgerUses.push(); ledgerUses.pop();
         LedgerUse storage w = ledgerUses[i]; w = ledgerUses[x]; u = ledgerUses.push();
         buckets[x].tokens[i + 1] = tok;
         Person memory m = alice; persons[i + 1] = m; Token memory t = tok;
         buckets[x].tokens[i] = t; ] true }

run_meta agree ts `Solidity.Examples.Tactics.Step.suiteArrays suiteArraysφ

end Suite

/-! ## Calls -/

section Calls

local instance : InContract := ⟨CallsExample⟩

private def ce : Expr := mkConst ``CallsExample

/-- `internalCallExpand` with a result, a nested call, `functionCallArgCapture`,
a call with no result. -/
private def callsφ : Fml CallsExample [] :=
  dl!{ [ uint y = addOne(4); uint z = addTwo(y); uint w = addOne(y + 1); credit(y, 5); bump();
         uint v = larger(z, w + 1); ] true }

run_meta agree ce `Solidity.Examples.Tactics.Step.calls callsφ

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
private def retsφ : Fml Rets [] :=
  dl!{ [ uint a; uint b; (a, b) = pair(3); (a, b) = pair(a + 1); Person memory m = mk(2);
         Person memory n = mk(total + 1); uint y = n.age; Basket memory k; k.items = new uint[](3);
         basket.items = new uint[](a); uint[] memory xs = new uint[](2); ] true }

run_meta agree re `Solidity.Examples.Tactics.Step.rets retsφ

end Rets

/-! ## `try` -/

/-- A contract that pings another. -/
def Pinger : Contract := contract!{ uint pings; uint last; }

section Try

local instance : InContract := ⟨Pinger⟩

private def pe : Expr := mkConst ``Pinger

/-- `tryCallNoCallbackBox`. -/
private def tryBoxφ : Fml Pinger [] :=
  dl!{ [ try I(7).get() returns (uint v) { last = v; } catch Panic(uint c) { last = c; }
         catch { last = 0; }; pings = 1; ] true }

run_meta agree pe `Solidity.Examples.Tactics.Step.tryBox tryBoxφ

/-- `tryCallDiamond`. -/
private def tryDiamondφ : Fml Pinger [] :=
  dl!{ ⟨ try I(7).get() returns (uint v) { last = v; } catch { last = 0; }; ⟩ true }

run_meta agree pe `Solidity.Examples.Tactics.Step.tryDiamond tryDiamondφ

end Try

end Solidity.Examples.Tactics.Step
