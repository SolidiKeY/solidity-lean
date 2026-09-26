import Solidity.Calculus.Close
import Solidity.Theory.Storage

/-!
# A struct with a mapping, written and deleted — both layers

`Ledger` (`TestSuite`) is `nonce` beside the mapping `balances`.  The program
writes the field and two entries, deletes one entry, reads three places,
deletes the whole struct, and reads again (mini-solkey's
`Examples/LedgerDelete.lean`):

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
taken to its value one lemma at a time.  The read it cannot take is
`survives`: the theory's `delNode` drops every `at` member, because a `Seg`
carries no `MapField` (`Theory/Storage.lean`, "Delete").
-/

namespace Solidity.Examples.LedgerDelete

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
  apply unfold .storageIndexWrite_unfold_leftFst
  apply unfold .localValueDeclInitDrop
  apply update .localValueAssign
  apply unfold .storageLocalDeclInitDrop
  apply update .storageFieldReadBindLocalRoot
  apply unfold .localValueDeclInitDrop
  apply update .localValueAssign
  apply update .storageIndexWriteMappingSave
  -- `ledger.balances[2] = 20;`, the same way
  apply unfold .storageIndexWrite_unfold_leftFst
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
  apply unfold (Stmt.step _ _ _).taclet
  apply unfold .storageLocalDeclInitDrop
  apply update .storageFieldReadBindLocalRoot
  apply update .storageIndexReadMappingFind
  -- `uint kept = ledger.balances[2];`
  apply unfold .localValueDeclInitDrop
  apply unfold (Stmt.step _ _ _).taclet
  apply unfold .storageLocalDeclInitDrop
  apply update .storageFieldReadBindLocalRoot
  apply update .storageIndexReadMappingFind
  -- `uint before = ledger.nonce;`
  apply unfold .localValueDeclInitDrop
  apply update .storageFieldReadFind
  apply empty
  apply close
  sol_symex
  sol_close

/-- `delete ledger;` is `storageRootDelete`: one update. -/
theorem deleteLedger : ⊨ dl!{ [ ledger.nonce = 42; delete ledger; ] true } := by
  apply Proves.valid
  apply update .storageFieldWriteSave
  apply update .storageRootDelete
  apply empty
  apply close
  sol_symex
  sol_close

/-- What the local `x` holds after `P` runs from `TestSuite`'s initial store. -/
def localAfter (P : Prog TestSuite) (x : String) : Res Binding := do
  (← Prog.run State.testSuiteStore P).getEnv (.user x)

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
#eval localAfter ledgerProgram "after"

/-! `survives`: the mapping entry is not. -/

/--
info: Except.ok (Solidity.Semantics.Binding.val (Solidity.Semantics.PrimVal.int 20))
-/
#guard_msgs in
#eval localAfter ledgerProgram "survives"

/-! `ledger.nonce = 5; ledger.balances[1] = 10; delete ledger;
uint kept = ledger.balances[1]; delete ledger.balances[1]; uint nonce0 = ledger.nonce;
uint gone = ledger.balances[1];` — deleting the entry is what clears it:
`kept * 100 + nonce0 * 10 + gone` is `1000`. -/

/--
info: Except.ok (Solidity.Semantics.Binding.val (Solidity.Semantics.PrimVal.int 1000))
-/
#guard_msgs in
#eval localAfter sol{ ledger.nonce = 5; ledger.balances[1] = 10; delete ledger;
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

/-- `after`: after `delete ledger` the field is below the deleted location, and
reads the reset of what was there (`findDelAtFields`), which at `int` is `0`. -/
theorem nonceAfterDelete (s : Struct) : asInt (findSt (S5 s) [ledger, nonce]) = 0 := by
  rw [S5, show [ledger, nonce] = [ledger] ++ [nonce] from rfl,
    find_delAt_fields _ (by simp) (by simp) (by decide)]
  exact delValueCast_asInt _

end Store

end Solidity.Examples.LedgerDelete
