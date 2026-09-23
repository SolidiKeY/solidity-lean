import Solidity.Tactics.Derivation
import Solidity.Tactics.Rewrite
import Solidity.Semantics.DecEq

/-!
# A struct with a mapping, written and deleted — both layers, one rule at a time

`Ledger` is `nonce` beside the mapping `balances`.  The program writes the
field and two entries, deletes one entry, then deletes the whole struct.  The
calculus half runs it to the stacked `save`/`delAt` updates with `seq_steps`;
the theory half reads the storage those updates compose to with `theory_rw`,
whose rule list works like `rw`'s: the cursor on a rule shows the goal that
rule receives, and the end of its line the goal it leaves.

The theory half starts from an arbitrary store `s`, so no read is computed:
each one is the rules on its line.  `S1`…`S5` are the calculus's updates, one
per `storage :=`, with the alias `sp@UintMap` resolved to its path.

**The read that is not here** is a `balances` entry after `delete ledger`.
Solidity keeps it — a mapping survives the delete of its struct — but
`delNode` drops every `at` member, because a `Seg` carries no `MapField`
(`Theory/Rewrite.lean`, `selectDelNodeMap`).  A chain would prove `0`.
`StorageSteps.lean`'s `deleteLedgerMappingSurvives` leaves that read as an
update, which is as far as the calculus goes too.
-/

namespace Solidity.Examples

open Rules StandardExample SoliditySyntax Semantics

set_option maxHeartbeats 8000000

section
variable (φ : WrappedExpr)

/-- `ledger.nonce = 5; ledger.balances[1] = 10; ledger.balances[2] = 20;
delete ledger.balances[1]; delete ledger;` — nothing merges, so the endpoint is
every update in order. -/
theorem ledgerWriteThenDelete :
    [ seq!{ => <[ (ledger@@Ledger).nonce = 5; (ledger@@Ledger).balances[1] = 10;
                  (ledger@@Ledger).balances[2] = 20;
                  delete (ledger@@Ledger).balances[1]; delete (ledger@@Ledger) ]>(φ) } ]
      ⇝ᵘ* [ seq!{ => { storage := save(storage, (ledger@@Ledger).nonce, 5) }
                    { se@uint := defVal(uint) } { se@uint := 10 }
                    { sp@UintMap := (ledger@@Ledger).balances }
                    { storage := save(storage, sp@UintMap[1], se@uint) }
                    { se@uint := defVal(uint) } { se@uint := 20 }
                    { sp@UintMap := (ledger@@Ledger).balances }
                    { storage := save(storage, sp@UintMap[2], se@uint) }
                    { sp@UintMap := (ledger@@Ledger).balances }
                    { storage := delAt(storage, sp@UintMap[1]) }
                    { storage := delAt(storage, (ledger@@Ledger)) } (φ) } ] := by
  seq_steps [.storageFieldWriteSave, .storageIndexWriteUnfoldLeftFst,
             .localValueDeclInitDrop, .valueDeclSkip, .localValueAssign,
             .storagePlaceAlias, .storageIndexWriteMappingSave,
             .storageIndexWriteUnfoldLeftFst, .localValueDeclInitDrop,
             .valueDeclSkip, .localValueAssign, .storagePlaceAlias,
             .storageIndexWriteMappingSave, .storageIndexDeleteUnfoldLeftFst,
             .storagePlaceAlias, .storageIndexDelete, .storageRootDelete]

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
