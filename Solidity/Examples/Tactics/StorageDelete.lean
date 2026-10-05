import Solidity.Calculus.Close
import Solidity.Calculus.Rewrite

/-!
# `delete`, rule by rule

The storage `delete` (the delete programs
of solkey's `taclets` suite), and what happens when you *read* after one
(mini-solkey's `Examples/Tactics/StorageDelete.lean`).

`delete` never writes a value the program names.  Its update is a marker,
`{ storage := delAt(storage, p) }`: the storage with the location at `p` reset
to its type's default, keeping the shape (`SVal.defaultOf`: an array keeps its
extent, a struct its mapping members).  Reading it back:

| read at | closes by | example |
|---|---|---|
| `p` itself, after a write to `p` | `sol_close` | `deleteThenRead` |
| `p` itself, in the sequent | the Theory's lemmas (`sol_rw`) | `deleteReadDeep_theory` |
| a path apart from `p` | `sol_close` | `deleteThenReadBeside` |
| a path apart from `p`, in the sequent | the Theory's lemmas (`sol_rw`) | `deleteFrame_theory` |
| a path apart from `p`, mid-program | the same, with the program still to run | `deleteFrameMid_theory` |
| a member below `p` | a run from the initial store | the `#eval`s at the end |
| `p`, with nothing known of it | not valid | `deleteRootUnknown` |

A read *below* a deleted struct reads the default of a member of a value
`sol_close` does not know (`Close.lean`), so those claims are checked on a run
of the interpreter from `State.exampleStore`, printed by `#eval`: a `Person`'s
default is built by the well-founded `defaultForTy`, which `rfl` cannot unfold.

The walks start with `apply Proves.valid`, which turns `⊨ φ` into the judgement
`⊢ φ`; each `apply` names one taclet (`StorageSteps.lean`).
-/

namespace Solidity.Examples.Tactics.StorageDelete

open Proves Semantics

local instance : InContract := ⟨StandardExample⟩

/-! ## Example 15: `delete alice.account;` — a simple receiver

`alice` is a root, so `alice.account` is `sp.fld` with `sp` simple: Step 3 at
once. -/

/-- `delete alice.account;` -/
theorem deleteField : ⊨ dl!{ [ delete alice.account; ] true } := by
  apply Proves.valid
  apply update .storageFieldDelete
  apply empty
  refine close ?_
  sol_symex
  sol_close

/-! ## Example 16: `delete alice.account.token;` — a non-simple receiver

`storageFieldDelete_unfold_leftFst` aliases the receiver `alice.account`
(Step 2), the alias declaration becomes an update, and `storageFieldDelete`
applies to `sp1.token`. -/

/-- `delete alice.account.token;` -/
theorem deleteDeepField : ⊨ dl!{ [ delete alice.account.token; ] true } := by
  apply Proves.valid
  apply unfold .storageFieldDelete_unfold_leftFst
  -- dl{ ⟹ [ Account storage sp1 = alice.account; delete sp1.token; ] true }
  apply unfold .storageLocalDeclInitDrop
  apply update .storageFieldReadBindLocalRoot
  apply update .storageFieldDelete
  apply empty
  refine close ?_
  sol_symex
  sol_close

/-! ## Example 17: `delete people[i];` — an entry -/

/-- `delete people[i];` -/
theorem deleteIndex : ⊨ dl!{ [ delete people[i]; ] true } := by
  apply Proves.valid
  apply update .storageIndexArrayDelete
  apply empty
  refine close ?_
  sol_symex
  sol_close

/-- `delete people[i + 1];` — a non-simple index is captured first
(`storageIndexDeleteNonSimpleIndexCapture`). -/
theorem deleteNonSimpleIndex : ⊨ dl!{ [ delete people[i + 1]; ] true } := by
  apply Proves.valid
  apply unfold .storageIndexDeleteNonSimpleIndexCapture
  apply unfold .localValueDeclInitDrop
  apply update .binopAssignment
  apply update .storageIndexArrayDelete
  apply empty
  refine close ?_
  sol_symex
  sol_close

/-! ## Reading after a delete -/

/-- `age = 10; delete age; uint result = age;` — a root reset reads `0`
(`storageRootDelete`, `storage-root-delete.key`). -/
theorem deleteThenRead :
    ⊨ dl!{ [ age = 10; delete age; uint result = age; ] result == 0 } := by
  apply Proves.valid
  apply update .storageRootWriteStore
  apply update .storageRootDelete
  apply unfold .localValueDeclInitDrop
  apply update .storageRootReadSelect
  apply empty
  refine close ?_
  sol_symex
  sol_close

/-- `alice.age = 30; delete alice.age; uint result = alice.age;`
(`storage-field-delete.key`). -/
theorem deleteFieldThenRead :
    ⊨ dl!{ [ alice.age = 30; delete alice.age; uint result = alice.age; ] result == 0 } := by
  sol_symex
  sol_close

/-- `values[1] = 7; delete values[1]; uint result = values[1];` — an array entry
(`storage-index-delete.key`). -/
theorem deleteIndexThenRead :
    ⊨ dl!{ [ values[1] = 7; delete values[1]; uint result = values[1]; ] result == 0 } := by
  sol_symex
  sol_close

/-- `flags[3] = true; delete flags[3]; bool result = flags[3];` — a `bool`
resets to `false` (`storage-index-delete-mapping-bool.key`). -/
theorem deleteBoolThenRead :
    ⊨ dl!{ [ flags[3] = true; delete flags[3]; bool result = flags[3]; ] result == false } := by
  sol_symex
  sol_close

/-! ## Reading after a delete, in the sequent

The same reads, closed as mini-solkey closes them: the calculus steps
(`sol_derive`), the updates merged into one parallel update (`Proves.merge`
for the locals, `Proves.mergeStorage` for a storage write), and the read the
last element binds rewritten by the Theory's own lemmas — `find_delAt_same`,
`find_copyTo_same`, `find_delAt_frame` of `Theory/Storage.lean` and
`Theory/Copy.lean`, named directly (`sol_rw`, `Calculus/TheoryRewrite.lean`).
The read sits in an update's right-hand side, `{ x := find(…) }`, which the
rewrite reaches because its result is a literal and the update is under the
box (`Proves.updRw`).  Then the update is applied to the goal and dropped
(`sol_apply_upd`) and `v = v` closes (`Proves.eqDClose`).  Every step is a
rule of the calculus, so none of them waits for the program to be gone
(`deleteFrameMid_theory`). -/

open Theory Theory.StValue in
/-- `alice.account.balance = 5; delete alice.account.balance;` read two
members down: `find_delAt_same` reads the delete, `find_copyTo_same` and
`copyVal` the write under it, and `delValueDefault`/`primDefault` reset the
word, in one step, since `delValue (findSt …)` alone is no term. -/
theorem deleteReadDeep_theory :
    ⊢ dl!{ [ alice.account.balance = 5; delete alice.account.balance;
      uint x = alice.account.balance; ] x == 0 } := by
  sol_derive
  -- dl{ { se1 := 5 }, { sp1 := alice.account }, { storage := save(storage, sp1.balance, se1) },
  --     { sp2 := alice.account }, { storage := delAt(storage, sp2.balance) },
  --     { sp3 := alice.account }, { x := find(storage, sp3.balance) } ⟹ x = 0 }
  refine Proves.merge rfl ?_
  refine Proves.mergeStorage ?_
  refine Proves.merge rfl ?_
  refine Proves.mergeStorage ?_
  refine Proves.merge rfl ?_
  refine Proves.merge rfl ?_
  -- dl{ { se1 := 5 ‖ … ‖ x := find(delAt(save(storage, alice.account.balance, 5),
  --       alice.account.balance), alice.account.balance) } ⟹ x = 0 }
  sol_rw [find_delAt_same, find_copyTo_same, copyVal, delValueDefault, primDefault]
  -- dl{ { se1 := 5 ‖ … ‖ x := 0 } ⟹ x = 0 }
  sol_apply_upd
  -- dl{ ⟹ 0 = 0 }
  exact Proves.eqDClose

open Theory Theory.StValue in
/-- `bob.age = 7; delete alice;` read at `bob.age`: the delete is off the
path (`find_delAt_frame`, its `diverges` decided on the two literal paths),
and the write is read back (`find_copyTo_same`, `copyVal`). -/
theorem deleteFrame_theory :
    ⊢ dl!{ [ bob.age = 7; delete alice; uint x = bob.age; ] x == 7 } := by
  sol_derive
  -- dl{ { storage := save(storage, bob.age, 7) }, { storage := delAt(storage, alice) },
  --     { x := find(storage, bob.age) } ⟹ x = 7 }
  refine Proves.mergeStorage ?_
  refine Proves.mergeStorage ?_
  sol_rw [find_delAt_frame, find_copyTo_same, copyVal]
  -- dl{ { storage := save(storage, bob.age, 7) ‖ storage := delAt(…) ‖ x := 7 } ⟹ x = 7 }
  sol_apply_upd
  exact Proves.eqDClose

open Theory Theory.StValue in
/-- The same read, rewritten while `x = x + 1;` is still to run: the merge
and the rewrite are rules of the calculus, not steps after it. -/
theorem deleteFrameMid_theory :
    ⊢ dl!{ [ bob.age = 7; delete alice; uint x = bob.age; x = x + 1; ] x == 8 } := by
  apply update .storageFieldWriteSave
  apply update .storageRootDelete
  apply unfold .localValueDeclInitDrop
  apply update .storageFieldReadFind
  refine Proves.mergeStorage ?_
  refine Proves.mergeStorage ?_
  sol_rw [find_delAt_frame, find_copyTo_same, copyVal]
  -- dl{ { storage := save(storage, bob.age, 7) ‖ storage := delAt(…) ‖ x := 7 } ⟹
  --     [ x = x + 1; ] x = 8 }
  sol_derive
  sol_apply_upd
  sol_apply_upd
  -- dl{ ⟹ 7 + 1 = 8 }
  refine close ?_
  sol_close

/-- `alice.account.balance = 7; alice.age = 30; delete alice.account;
uint a = alice.age;` — `alice.age` parts ways with `alice.account` (at `age`
against `account`), so it keeps `30`. -/
theorem deleteThenReadBeside :
    ⊨ dl!{ [ alice.account.balance = 7; alice.age = 30; delete alice.account;
             uint a = alice.age; ] a == 30 } := by
  apply Proves.valid
  apply unfold .storageFieldWrite_unfold_leftFst
  apply unfold .localValueDeclInitDrop
  apply update .localValueAssign
  apply unfold .storageLocalDeclInitDrop
  apply update .storageFieldReadBindLocalRoot
  apply update .storageFieldWriteSave
  apply update .storageFieldWriteSave
  apply update .storageFieldDelete
  apply unfold .localValueDeclInitDrop
  apply update .storageFieldReadFind
  apply empty
  refine close ?_
  sol_symex
  sol_close

/-- The storage in which `total` holds a `bool`. -/
def boolTotal : State := { State.exampleStore with storage := [("total", .bool true)] }

/-- `delete total;` then `total == 0` is **not** valid: `⊨` ranges over every
state, and where `total` holds a `bool` the delete resets it to `false`.  A
write first fixes what is there (`deleteThenRead`). -/
theorem deleteRootUnknown : ¬ (⊨ dl!{ [ delete total; ] total == 0 }) :=
  fun h => by obtain ⟨x, hx, hy⟩ := holds_eqD_iff.1 (h boolTotal).1; cases hx; cases hy

/-! ### Below a deleted struct, from the initial store

`alice.account.balance = 100; alice.account.token.value = 7; delete alice.account;`
then both members read back as `0`. -/

/--
info: Except.ok (Solidity.Semantics.Binding.val (Solidity.Semantics.PrimVal.int 0))
-/
#guard_msgs in
#eval Prog.localAfter State.exampleStore (sol{
    alice.account.balance = 100; alice.account.token.value = 7; delete alice.account;
    uint b = alice.account.balance; uint v = alice.account.token.value; uint r = b + v;
  } : Prog StandardExample) "r"

/-! `alice.age = 30; delete alice; uint result = alice.age;` (`storage-root-delete-struct.key`). -/

/--
info: Except.ok (Solidity.Semantics.Binding.val (Solidity.Semantics.PrimVal.int 0))
-/
#guard_msgs in
#eval Prog.localAfter State.exampleStore (sol{
    alice.age = 30; delete alice; uint result = alice.age;
  } : Prog StandardExample) "result"

/-! `folks[1].age = 44; delete folks[1]; uint result = folks[1].age;` — a struct
entry of a mapping (`storage-index-delete-mapping-struct.key`). -/

/--
info: Except.ok (Solidity.Semantics.Binding.val (Solidity.Semantics.PrimVal.int 0))
-/
#guard_msgs in
#eval Prog.localAfter State.exampleStore (sol{
    folks[1].age = 44; delete folks[1]; uint result = folks[1].age;
  } : Prog StandardExample) "result"

/-! A struct's mapping members survive its `delete` (solkey `selectStDelNodeMap`),
its value members do not (`selectStDelNodePrim`): after
`wallet.owner = 7; wallet.stash[1] = 42; delete wallet;` the entry is `42` and
the owner `0`. -/

/--
info: Except.ok (Solidity.Semantics.Binding.val (Solidity.Semantics.PrimVal.int 42))
-/
#guard_msgs in
#eval Prog.localAfter State.exampleStore (sol{
    wallet.owner = 7; wallet.stash[1] = 42; delete wallet; uint kept = wallet.stash[1];
  } : Prog StandardExample) "kept"

/--
info: Except.ok (Solidity.Semantics.Binding.val (Solidity.Semantics.PrimVal.int 0))
-/
#guard_msgs in
#eval Prog.localAfter State.exampleStore (sol{
    wallet.owner = 7; wallet.stash[1] = 42; delete wallet; uint o = wallet.owner;
  } : Prog StandardExample) "o"

/-! ## A fixed-size array keeps its length

`delete` of a `uint[3]` resets its three elements in place and keeps the
length (solc; solkey's `delNodeFixed`), where a `uint[]` is emptied.  The
interpreter knows which by the value (`SVal.array`'s `fixed`), so the rule is
the same `storageRootDelete`; `sol_decide` reads it back by a case on the
location's shape (`Examples/Tactics/Decide.lean`, `fixedDelete`). -/

section Fixed

local instance : InContract := ⟨TestSuite⟩

/-! From the initial store, solkey's `testFixedArrayDeleteKeepsLength`,
`testFixedStructArrayDeleteResetsElements`,
`testStructWithFixedArrayDeleteKeepsLength`, `testStructWithFixedArrayCopy`
and `testFixedMappingArrayDeleteKeepsEntries`: each run ends normally. -/

/-- info: [true, true, true, true, true] -/
#guard_msgs in
#eval [
  (Prog.run State.testSuiteStore (sol{ require(2 < fixedValues.length); fixedValues[1] = 7;
    delete fixedValues; assert(2 < fixedValues.length); assert(fixedValues[1] == 0); })).isOk,
  (Prog.run State.testSuiteStore (sol{ require(1 < fixedTokens.length);
    fixedTokens[1].value = 7; delete fixedTokens; assert(1 < fixedTokens.length);
    assert(fixedTokens[1].value == 0); })).isOk,
  (Prog.run State.testSuiteStore (sol{ require(2 < triple.items.length); triple.items[1] = 7;
    triple.tag = 3; delete triple; assert(2 < triple.items.length);
    assert(triple.items[1] == 0); assert(triple.tag == 0); })).isOk,
  (Prog.run State.testSuiteStore (sol{ require(2 < triple.items.length); triple.items[1] = 7;
    triple2 = triple; assert(triple2.items[1] == 7); })).isOk,
  (Prog.run State.testSuiteStore (sol{ require(1 < fixedMaps.length); fixedMaps[1][2] = 5;
    delete fixedMaps; assert(fixedMaps[1][2] == 5); })).isOk]

end Fixed

end Solidity.Examples.Tactics.StorageDelete
