import Solidity.Calculus.Close
import Solidity.Theory.Storage

/-!
# A struct with a mapping, written and deleted — both layers

`Ledger` (`TestSuite`) is `nonce` beside the mapping `balances`.  The program
writes the field and two entries, deletes one entry, reads three places,
deletes the whole struct, and reads again (mini-solkey's
`Examples/Tactics/LedgerDelete.lean`):

```solidity
ledger.nonce = 5; ledger.balances[1] = 10; ledger.balances[2] = 20;
delete ledger.balances[1];
uint gone = ledger.balances[1]; uint kept = ledger.balances[2]; uint before = ledger.nonce;
delete ledger;
uint after = ledger.nonce; uint survives = ledger.balances[2];
```

**Part 1** runs the calculus on the program up to the struct delete, rule by
rule, and closes the three reads with `sol_close`.  The two reads after
`delete ledger` are below the deleted location, which `sol_close` does not
read (`StorageDelete.lean`), so they are a run of the interpreter from
`TestSuite`'s initial store: `after` is `0`, and `survives` is `20` — `delete`
cannot clear a mapping, since it does not know the keys, and the interpreter
keeps every entry (`SVal.defaultOf`).

**Part 2** is the storage theory, by hand: the same storages
written as terms of `structRules.key`'s algebra over an arbitrary store `s`
(`Theory/Storage.lean`), `S1`…`S5` one per `storage :=` update, and each read
taken to its value one lemma at a time.  The two reads after `delete ledger`
carry the sorts the program's types give: `ledger` is not a mapping, and
`ledger.balances` is one, so its entry survives (`selectDelNodeMap`,
`Theory/Storage.lean`, "Delete").
-/

namespace Solidity.Examples.Tactics.LedgerDelete

open Proves Semantics

local instance : InContract := ⟨TestSuite⟩

/-! ## Part 1 · The calculus -/

/-- `ledger.nonce = 5; ledger.balances[1] = 10; ledger.balances[2] = 20;
delete ledger.balances[1]; uint gone = ledger.balances[1];
uint kept = ledger.balances[2]; uint before = ledger.nonce;` -/
theorem ledgerWriteThenDelete :
    ⊨ dl!{ [ ledger.nonce = 5; ledger.balances[1] = 10; ledger.balances[2] = 20;
             delete ledger.balances[1];
             uint gone = ledger.balances[1]; uint kept = ledger.balances[2];
             uint before = ledger.nonce; ]
           gone == 0 && kept == 20 && before == 5 } := by
  apply Proves.valid
  apply update .storageFieldWriteSave
  -- `ledger.balances[1] = 10;`: source, receiver `ledger.balances`, index
  apply unfold .storageIndexWriteCaptureAllComplexRecv
  apply unfold .localValueDeclInitDrop
  apply update .localValueAssign
  apply unfold .storageLocalDeclInitDrop
  apply update .storageFieldReadBindLocalRoot
  apply unfold .localValueDeclInitDrop
  apply update .localValueAssign
  apply update .storageIndexWriteMappingSave
  -- `ledger.balances[2] = 20;`, the same way
  apply unfold .storageIndexWriteCaptureAllComplexRecv
  apply unfold .localValueDeclInitDrop
  apply update .localValueAssign
  apply unfold .storageLocalDeclInitDrop
  apply update .storageFieldReadBindLocalRoot
  apply unfold .localValueDeclInitDrop
  apply update .localValueAssign
  apply update .storageIndexWriteMappingSave
  -- `delete ledger.balances[1];`: the receiver aliased, then `delAt`
  apply unfold .storageIndexDelete_unfold_leftFst
  apply unfold .storageLocalDeclInitDrop
  apply update .storageFieldReadBindLocalRoot
  apply update .storageIndexDelete
  -- `uint gone = ledger.balances[1];`: Step 1 (`storageIndexRead_unfold_rightFst`,
  -- by the strategy: its conclusion is a `Hole.fill`, see `StorageSteps.lean`)
  apply unfold .localValueDeclInitDrop
  apply unfoldRule (Stmt.step _ _ _).rule
  apply unfold .storageLocalDeclInitDrop
  apply update .storageFieldReadBindLocalRoot
  apply update .storageIndexReadMappingFind
  -- `uint kept = ledger.balances[2];`
  apply unfold .localValueDeclInitDrop
  apply unfoldRule (Stmt.step _ _ _).rule
  apply unfold .storageLocalDeclInitDrop
  apply update .storageFieldReadBindLocalRoot
  apply update .storageIndexReadMappingFind
  -- `uint before = ledger.nonce;`
  apply unfold .localValueDeclInitDrop
  apply update .storageFieldReadFind
  apply empty
  refine close ?_
  sol_symex
  sol_close

/-- `delete ledger;` is `storageRootDelete`: one update. -/
theorem deleteLedger : ⊨ dl!{ [ ledger.nonce = 42; delete ledger; ] true } := by
  apply Proves.valid
  apply update .storageFieldWriteSave
  apply update .storageRootDelete
  apply empty
  refine close ?_
  sol_symex
  sol_close

/-- The whole program. -/
def ledgerProgram : Prog TestSuite := sol{
  ledger.nonce = 5; ledger.balances[1] = 10; ledger.balances[2] = 20;
  delete ledger.balances[1];
  uint gone = ledger.balances[1]; uint kept = ledger.balances[2]; uint before = ledger.nonce;
  delete ledger;
  uint after = ledger.nonce; uint survives = ledger.balances[2];
}

/-! `after`: the value member is reset by `delete ledger`. -/

/--
info: Except.ok (Solidity.Semantics.Binding.val (Solidity.Semantics.PrimVal.int 0))
-/
#guard_msgs in
#eval Prog.localAfter State.testSuiteStore ledgerProgram "after"

/-! `survives`: the mapping entry is not. -/

/--
info: Except.ok (Solidity.Semantics.Binding.val (Solidity.Semantics.PrimVal.int 20))
-/
#guard_msgs in
#eval Prog.localAfter State.testSuiteStore ledgerProgram "survives"

/-! `ledger.nonce = 5; ledger.balances[1] = 10; delete ledger;
uint kept = ledger.balances[1]; delete ledger.balances[1]; uint nonce0 = ledger.nonce;
uint gone = ledger.balances[1];` — deleting the entry is what clears it:
`kept * 100 + nonce0 * 10 + gone` is `1000`. -/

/--
info: Except.ok (Solidity.Semantics.Binding.val (Solidity.Semantics.PrimVal.int 1000))
-/
#guard_msgs in
#eval Prog.localAfter State.testSuiteStore
  sol{ ledger.nonce = 5; ledger.balances[1] = 10; delete ledger;
       uint kept = ledger.balances[1]; delete ledger.balances[1];
       uint nonce0 = ledger.nonce; uint gone = ledger.balances[1];
       uint r = kept * 100 + nonce0 * 10 + gone; } "r"

/-! ## Part 2 · The storage theory, by hand -/

namespace Store

open Theory Theory.StValue

abbrev ledger   : Seg := .field "ledger"
abbrev nonce    : Seg := .field "nonce"
abbrev balances : Seg := .field "balances"

/-- The storages of the program, one per `storage :=` update. -/
def S1 (s : Struct) : Struct := save s [ledger, nonce] (int 5)
def S2 (s : Struct) : Struct := save (S1 s) [ledger, balances, .at 1] (int 10)
def S3 (s : Struct) : Struct := save (S2 s) [ledger, balances, .at 2] (int 20)
def S4 (s : Struct) : Struct := delAt (S3 s) [ledger, balances, .at 1]
def S5 (s : Struct) : Struct := delAt (S4 s) [ledger]

/-- `gone`: the deleted entry reads as the default. -/
theorem deletedEntry (s : Struct) : findSt (S4 s) [ledger, balances, .at 1] = int 0 := by
  rw [S4, find_delAt_same _ (by simp)]        -- `findDelAt`: the deleted value
  rw [S3, find_save_frame _ _ _ _ (by decide)] -- `findOnSaveDifferent`: past key 2
  rw [S2, find_save_same _ (by simp)]          -- `findOnSave`: the write of key 1
  rfl                                          -- `delValueDefault`

/-- The same chain with every intermediate term written down. -/
theorem deletedEntryWritten (s : Struct) :
    findSt (S4 s) [ledger, balances, .at 1] = int 0 :=
  calc findSt (S4 s) [ledger, balances, .at 1]
      _ = delValue (findSt (S3 s) [ledger, balances, .at 1]) := find_delAt_same _ (by simp)
      _ = delValue (findSt (S2 s) [ledger, balances, .at 1]) := by
            rw [S3, find_save_frame _ _ _ _ (by decide)]
      _ = delValue (int 10)                                  := by rw [S2, find_save_same _ (by simp)]
      _ = prim (primDefault (.int 10))                       := delValueDefault _
      _ = int 0                                              := rfl

/-- `kept`: the entry beside it does not see the delete. -/
theorem survivingEntry (s : Struct) : findSt (S4 s) [ledger, balances, .at 2] = int 20 := by
  rw [S4, find_delAt_frame _ (by decide)]      -- `findDelAtOutside`: key 1 and key 2 part ways
  rw [S3, find_save_same _ (by simp)]

/-- `before`: neither does the field; two frames past the entries, then the
write. -/
theorem nonceBeforeDelete (s : Struct) : findSt (S4 s) [ledger, nonce] = int 5 := by
  rw [S4, find_delAt_frame _ (by decide)]
  rw [S3, find_save_frame _ _ _ _ (by decide), S2, find_save_frame _ _ _ _ (by decide)]
  rw [S1, find_save_same _ (by simp)]

/-- A write below `ledger` leaves the kind of what `ledger` holds. -/
private theorem kind_ledger_save (s : Struct) {r : List Seg} (hr : r ≠ []) (v : StValue) :
    (asStruct (findSt (save s (ledger :: r) v) [ledger])).kind =
      (asStruct (findSt s [ledger])).kind := by
  rw [show ledger :: r = [ledger] ++ r from rfl, find_save_prefix _ _ hr, asStruct_st,
    kind_save _ hr]

/-- …and one below `ledger.balances` the kind of what that holds. -/
private theorem kind_balances_save (s : Struct) {r : List Seg} (hr : r ≠ []) (v : StValue) :
    (asStruct (findSt (save s (ledger :: balances :: r) v) [ledger, balances])).kind =
      (asStruct (findSt s [ledger, balances])).kind := by
  rw [show ledger :: balances :: r = [ledger, balances] ++ r from rfl, find_save_prefix _ _ hr,
    asStruct_st, kind_save _ hr]

/-- `after`: after `delete ledger` the field is below the deleted location, and
reads the reset of what was there (`findDelAt` one member down), which at `int`
is `0`.  The premise is `ledger`'s sort: a struct, not a mapping. -/
theorem nonceAfterDelete (s : Struct) (hk : (asStruct (findSt s [ledger])).kind ≠ some .map) :
    asInt (findSt (S5 s) [ledger, nonce]) = 0 := by
  have hk4 : (asStruct (findSt (S4 s) [ledger])).kind ≠ some .map := by
    rw [S4, delAt, kind_ledger_save _ (by simp), S3, kind_ledger_save _ (by simp), S2,
      kind_ledger_save _ (by simp), S1, kind_ledger_save _ (by simp)]
    exact hk
  rw [S5, show [ledger, nonce] = [ledger] ++ [nonce] from rfl,
    find_delAt_member _ (by simp) _ (keepsOnDelete_field hk4 (by decide))]
  exact delValueCast_asInt _

/-- `survives`: `ledger.balances` is a mapping, so `delete ledger` keeps its
entries (`selectDelNodeMap`): the entry reads what it read before. -/
theorem balancesSurvive (s : Struct)
    (hm : (asStruct (findSt s [ledger, balances])).kind = some .map) :
    findSt (S5 s) [ledger, balances, .at 2] = findSt (S4 s) [ledger, balances, .at 2] := by
  have hm4 : (asStruct (findSt (S4 s) [ledger, balances])).kind = some .map := by
    rw [S4, delAt, kind_balances_save _ (by simp), S3, kind_balances_save _ (by simp), S2,
      kind_balances_save _ (by simp), S1, find_save_frame _ _ _ _ (by decide)]
    exact hm
  rw [S5, show [ledger, balances, .at 2] = [ledger] ++ [balances, .at 2] from rfl,
    find_delAt_extends _ (by simp) (by simp), delValueCast]
  exact selectDelNodeMap hm4

end Store

end Solidity.Examples.Tactics.LedgerDelete
