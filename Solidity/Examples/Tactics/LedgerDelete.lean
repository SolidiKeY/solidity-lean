import Solidity.Tools.Run
import Solidity.Calculus.Close
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
import Solidity.Tools.Inspect

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

**Part 2** is the storage theory, by hand: the same storages written in the
typed Theory over an arbitrary storage `s` (`Theory/Typed/Obs.lean`, a
storage its observations at typed locations), `S1`…`S5` one per `storage :=`
update, and each read taken to its value one law at a time.  The two reads
after `delete ledger` need no premise: the delete is read off the type
(`TVal.delR`), `ledger` a struct whose `nonce` is reset, `ledger.balances` a
mapping whose entries a delete keeps.
-/

namespace Solidity.Examples.Tactics.LedgerDelete

open Semantics

local instance : InContract := ⟨TestSuite⟩

open scoped Scoped

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
  apply unfoldStep
  apply unfold .storageLocalDeclInitDrop
  apply update .storageFieldReadBindLocalRoot
  apply update .storageIndexReadMappingFind
  -- `uint kept = ledger.balances[2];`
  apply unfold .localValueDeclInitDrop
  apply unfoldStep
  apply unfold .storageLocalDeclInitDrop
  apply update .storageFieldReadBindLocalRoot
  apply update .storageIndexReadMappingFind
  -- `uint before = ledger.nonce;`
  apply unfold .localValueDeclInitDrop
  apply update .storageFieldReadFind
  apply empty
  sol_leaf
  sol_decide

/-- `delete ledger;` is `storageRootDelete`: one update. -/
theorem deleteLedger : ⊨ dl!{ [ ledger.nonce = 42; delete ledger; ] true } := by
  apply Proves.valid
  apply update .storageFieldWriteSave
  apply update .storageRootDelete
  apply empty
  sol_leaf
  sol_close

/-- The whole program. -/
def ledgerProgram := (sol{
  ledger.nonce = 5; ledger.balances[1] = 10; ledger.balances[2] = 20;
  delete ledger.balances[1];
  uint gone = ledger.balances[1]; uint kept = ledger.balances[2]; uint before = ledger.nonce;
  delete ledger;
  uint after = ledger.nonce; uint survives = ledger.balances[2];
} : Prog TestSuite [] _)

/-! `after`: the value member is reset by `delete ledger`. -/

/--
info: Except.ok (some (Solidity.Semantics.PrimVal.int 0))
-/
#guard_msgs in
#eval Prog.localAfterT State.testSuiteStore ledgerProgram "after"

/-! `survives`: the mapping entry is not. -/

/--
info: Except.ok (some (Solidity.Semantics.PrimVal.int 20))
-/
#guard_msgs in
#eval Prog.localAfterT State.testSuiteStore ledgerProgram "survives"

/-! `ledger.nonce = 5; ledger.balances[1] = 10; delete ledger;
uint kept = ledger.balances[1]; delete ledger.balances[1]; uint nonce0 = ledger.nonce;
uint gone = ledger.balances[1];` — deleting the entry is what clears it:
`kept * 100 + nonce0 * 10 + gone` is `1000`. -/

/--
info: Except.ok (some (Solidity.Semantics.PrimVal.int 1000))
-/
#guard_msgs in
#eval Prog.localAfterT State.testSuiteStore
  sol{ ledger.nonce = 5; ledger.balances[1] = 10; delete ledger;
       uint kept = ledger.balances[1]; delete ledger.balances[1];
       uint nonce0 = ledger.nonce; uint gone = ledger.balances[1];
       uint r = kept * 100 + nonce0 * 10 + gone; } "r"

/-! ## Part 2 · The storage theory, by hand -/

namespace Store

/-- `ledger`, `ledger.nonce` and `ledger.balances[k]`: storage locations of
`TestSuite` (`SLoc`), typed by what they hold. -/
abbrev ledger : SLoc TestSuite (.ref (.struct "Ledger")) := .ref (SRef.ofRoot "ledger" rfl)
abbrev nonce : SLoc TestSuite .uint := ObsLoc.app ledger (.field (f := "nonce") rfl .nil)
abbrev balance (k : Int) : SLoc TestSuite .uint :=
  ObsLoc.app ledger (.field (f := "balances") rfl (.key (K := .uint) k .nil))

/-- A word as written. -/
abbrev w (n : Int) (h : PrimTy.uint.inRange n = true := by rfl) : PrimTy.uint.Denote := ⟨n, h⟩

/-- The storages of the program, one per `storage :=` update, over any
storage `s`. -/
def S1 (s : TSto TestSuite) : TSto TestSuite := s.copyTo nonce (TVal.ofWord (w 5))
def S2 (s : TSto TestSuite) : TSto TestSuite := (S1 s).copyTo (balance 1) (TVal.ofWord (w 10))
def S3 (s : TSto TestSuite) : TSto TestSuite := (S2 s).copyTo (balance 2) (TVal.ofWord (w 20))
def S4 (s : TSto TestSuite) : TSto TestSuite := (S3 s).delAt (balance 1)
def S5 (s : TSto TestSuite) : TSto TestSuite := (S4 s).delAt ledger

/-- `gone`: the deleted entry reads its default, whatever was written there
(`findOnDelAt`). -/
theorem deletedEntry (s : TSto TestSuite) : (S4 s).word (balance 1) = w 0 :=
  Obs.findOnDelAt _ _

/-- `kept`: the entry beside it does not see the delete (`findOnDelAtFrame`,
key 1 and key 2 part ways), and reads its write (`findOnSave`). -/
theorem survivingEntry (s : TSto TestSuite) : (S4 s).word (balance 2) = w 20 := by
  rw [S4, Obs.findOnDelAtFrame (p := balance 1) _ (by decide +kernel), S3, Obs.findOnSave]; rfl

/-- `before`: neither does the field; two frames past the entries, then the
write. -/
theorem nonceBeforeDelete (s : TSto TestSuite) : (S4 s).word nonce = w 5 := by
  rw [S4, Obs.findOnDelAtFrame (p := balance 1) (q := nonce) _ (by decide +kernel), S3,
    Obs.findOnSaveFrame (p := balance 2) (q := nonce) _ _ (by decide +kernel), S2,
    Obs.findOnSaveFrame (p := balance 1) (q := nonce) _ _ (by decide +kernel), S1, Obs.findOnSave]
  rfl

/-- `after`: after `delete ledger` the field is below the deleted location,
and the delete resets it: `ledger` is a struct, `nonce` a word of it
(`TVal.delR`, read off the type). -/
theorem nonceAfterDelete (s : TSto TestSuite) : (S5 s).word nonce = w 0 := by
  rw [S5, Obs.delAt_word_below]; rfl

/-- `survives`: `ledger.balances` is a mapping, so `delete ledger` keeps its
entries (the delete reads past a key, `TVal.delR`): the entry reads what it
read before. -/
theorem balancesSurvive (s : TSto TestSuite) : (S5 s).word (balance 2) = (S4 s).word (balance 2) := by
  rw [S5, Obs.delAt_word_below]
  show ((S4 s).find ledger).word ((Path.field _ .nil).append (.key 2 .nil)) = _
  rw [Path.append_field, Path.append_nil]
  rfl

end Store

end Solidity.Examples.Tactics.LedgerDelete
