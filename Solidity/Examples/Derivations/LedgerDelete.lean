import Solidity.Tactics.Derivation
import Solidity.Tactics.Rewrite
import Solidity.Semantics.DecEq

/-!
# A struct with a mapping, written and deleted — both layers, one proof

`Ledger` is `nonce` beside the mapping `balances`.  The program writes the
field and two entries, deletes one entry, reads three places, deletes the
whole struct and reads the field again.  `ledgerWriteThenDelete` is one proof
of all of it: `seq_steps` runs the calculus to the stacked `save`/`delAt`
updates, and `theory_rw` turns each read into a term of the storage theory over
the storage the line started from (`seq_lower`, `Update/Lower.lean`), then
rewrites those terms as `rw` would, one rule at a time, until each read is a
literal.  The cursor on a rule shows the goal it receives.

The second half states the same reads over an arbitrary store `s`, with
`S1`…`S5` the calculus's updates written by hand, one per `storage :=`.

**The read that is not here** is a `balances` entry after `delete ledger`.
Solidity keeps it — a mapping survives the delete of its struct — but
`delNode` drops every `at` member, because a `Seg` carries no `MapField`
(`Theory/Rewrite.lean`, `selectDelNodeMap`).  A chain would prove `0`, and
`seq_lower` does not lower it: the theory's answer there is no literal.
`StorageSteps.lean`'s `deleteLedgerMappingSurvives` leaves that read as an
update, which is as far as the calculus goes too.
-/

namespace Solidity.Examples

open Rules StandardExample SoliditySyntax Semantics Theory.StValue

set_option maxHeartbeats 8000000

section
variable (φ : WrappedExpr)

/-- `ledger.nonce = 5; ledger.balances[1] = 10; ledger.balances[2] = 20;
delete ledger.balances[1]; gone = ledger.balances[1]; kept = ledger.balances[2];
before = ledger.nonce; delete ledger; after = ledger.nonce;` — the calculus's
stack, with each read taken to its value by the storage theory.  The four
lines of the `theory_rw` are the four reads in order. -/
theorem ledgerWriteThenDelete :
    [ seq!{ => <[ (ledger@@Ledger).nonce = 5; (ledger@@Ledger).balances[1] = 10;
                  (ledger@@Ledger).balances[2] = 20;
                  delete (ledger@@Ledger).balances[1];
                  gone = (ledger@@Ledger).balances[1]; kept = (ledger@@Ledger).balances[2];
                  before = (ledger@@Ledger).nonce;
                  delete (ledger@@Ledger); after = (ledger@@Ledger).nonce ]>(φ) } ]
      ⇝ᵘ* [ seq!{ => { storage := save(storage, (ledger@@Ledger).nonce, 5) }
                    { se@uint := defVal(uint) } { se@uint := 10 }
                    { sp@UintMap := (ledger@@Ledger).balances }
                    { storage := save(storage, sp@UintMap[1], se@uint) }
                    { se@uint := defVal(uint) } { se@uint := 20 }
                    { sp@UintMap := (ledger@@Ledger).balances }
                    { storage := save(storage, sp@UintMap[2], se@uint) }
                    { sp@UintMap := (ledger@@Ledger).balances }
                    { storage := delAt(storage, sp@UintMap[1]) }
                    { sp@UintMap := (ledger@@Ledger).balances } { gone := 0 }
                    { sp@UintMap := (ledger@@Ledger).balances } { kept := 20 }
                    { before := 5 }
                    { storage := delAt(storage, (ledger@@Ledger)) }
                    { after := 0 } (φ) } ] := by
  seq_steps [.storageFieldWriteSave, .storageIndexWriteUnfoldLeftFst,
             .localValueDeclInitDrop, .valueDeclSkip, .localValueAssign,
             .storagePlaceAlias, .storageIndexWriteMappingSave,
             .storageIndexWriteUnfoldLeftFst, .localValueDeclInitDrop,
             .valueDeclSkip, .localValueAssign, .storagePlaceAlias,
             .storageIndexWriteMappingSave, .storageIndexDeleteUnfoldLeftFst,
             .storagePlaceAlias, .storageIndexDelete,
             .storageIndexReadUnfoldRightFst, .storagePlaceAlias,
             .storageIndexReadMappingFind, .storageIndexReadUnfoldRightFst,
             .storagePlaceAlias, .storageIndexReadMappingFind,
             .storageFieldReadFind, .storageRootDelete, .storageFieldReadFind]
  theory_rw [.findDelAt, .findOnSaveDifferent, .findOnSave, .delValueDefault,
             .findDelAtOutside, .findOnSave,
             .findDelAtOutside, .findOnSaveDifferent, .findOnSaveDifferent, .findOnSave,
             .findDelAtFields, .findDelAtOutside, .findOnSaveDifferent,
             .findOnSaveDifferent, .findOnSave, .delValueDefault]

end

end Solidity.Examples

namespace Solidity.Examples.LedgerDelete

open Solidity.Theory Solidity.Theory.StValue Semantics

private abbrev ledger   : Seg := .field "ledger"
private abbrev nonce    : Seg := .field "nonce"
private abbrev balances : Seg := .field "balances"

private abbrev S1 (s : Struct) : Struct := save s [ledger, nonce] (StValue.int 5)
private abbrev S2 (s : Struct) : Struct := save (S1 s) [ledger, balances, .at 1] (StValue.int 10)
private abbrev S3 (s : Struct) : Struct := save (S2 s) [ledger, balances, .at 2] (StValue.int 20)
private abbrev S4 (s : Struct) : Struct := delAt (S3 s) [ledger, balances, .at 1]
private abbrev S5 (s : Struct) : Struct := delAt (S4 s) [ledger]

/-- The deleted entry reads as its default. -/
theorem deletedEntry (s : Struct) :
    findSt (S4 s) [ledger, balances, .at 1] = StValue.int 0 := by
  theory_rw [.findDelAt, .findOnSaveDifferent, .findOnSave, .delValueDefault]

/-- The same chain as a `sol_rewrite`, with every intermediate term written
down.  Compare it with `deletedEntry`, as `StorageSteps.lean` compares
`deepFieldWrite` with `deepFieldWriteListed`. -/
sol_rewrite deletedEntryWritten (s : Struct) :
    findSt (S4 s) [ledger, balances, .at 1]
  =[.findDelAt]           delValue (findSt (S3 s) [ledger, balances, .at 1])
  =[.findOnSaveDifferent] delValue (findSt (S2 s) [ledger, balances, .at 1])
  =[.findOnSave]          delValue (StValue.int 10)
  =[.delValueDefault]     StValue.prim (primDefault (.int 10))
  =                       StValue.int 0

/-- The entry beside it does not see the delete. -/
theorem survivingEntry (s : Struct) :
    findSt (S4 s) [ledger, balances, .at 2] = StValue.int 20 := by
  theory_rw [.findDelAtOutside, .findOnSave]

/-- Neither does the field, before the struct delete: two frames past the
entries, then the write. -/
theorem nonceBeforeDelete (s : Struct) :
    findSt (S4 s) [ledger, nonce] = StValue.int 5 := by
  theory_rw [.findDelAtOutside, .findOnSaveDifferent, .findOnSaveDifferent, .findOnSave]

/-- After `delete ledger` the field reads as `0`: a read below the deleted
path reads out of the deleted value, and a member of a deleted node reads as its
default.  Read at `int`, because that is where `selectDelNodeDefault` is stated. -/
theorem nonceAfterDelete (s : Struct) :
    asInt (findSt (S5 s) [ledger, nonce]) = 0 := by
  theory_rw [.findDelAtExtends, .delValueCast, .findSingleton, .selectDelNodeDefault]

end Solidity.Examples.LedgerDelete
