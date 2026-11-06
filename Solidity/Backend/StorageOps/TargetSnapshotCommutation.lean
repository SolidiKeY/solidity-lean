import Solidity.Backend.StorageOps.TargetFixedSnapshot

/-! Actual target snapshot sequence commutation. Cross-operation write/write
and read/write separation are explicit; intra-operation overlap is allowed. -/
namespace Solidity.Backend.StorageOps.TargetSnapshotCommutation
open TargetFixedSnapshot

private theorem store_ext (a b : Evm.WordStore) (same : ∀ s,a s=b s) : a=b := by
 cases a with
 | mk a =>
  cases b with
  | mk b =>
   have cells : a=b := funext (fun s => Fin.ext (same s))
   exact congrArg Evm.WordStore.mk cells

/-- Two independently captured snapshot operations commute when neither
changes the other's source and their generated destinations are disjoint.
There is no requirement that either operation's own source/destination differ. -/
theorem machines (pa pb : PrimTy) (ma mb : TypeGraph.FixedSize) (machine : Evm.Machine)
 (sa da sb db : Evm.Slot)
 (writes : ∀ i<ma.val,∀ j<mb.val,da.add i≠db.add j)
 (readA : ∀ i<ma.val,∀ j<mb.val,sa.add i≠db.add j)
 (readB : ∀ j<mb.val,∀ i<ma.val,sb.add j≠da.add i) :
 afterCopy pb mb (afterCopy pa ma machine sa da) sb db=
 afterCopy pa ma (afterCopy pb mb machine sb db) sa da := by
 classical
 have words : ∀ observer,
  (afterCopy pb mb (afterCopy pa ma machine sa da) sb db).store observer=
  (afterCopy pa ma (afterCopy pb mb machine sb db) sa da).store observer := by
  intro observer
  by_cases hitA : ∃ i,i<ma.val ∧ observer=da.add i
  · obtain ⟨i,inside,rfl⟩:=hitA
    rw [after_outside pb mb (afterCopy pa ma machine sa da) sb db (da.add i) (writes i inside)]
    rw [after_data pa ma machine sa da i inside,
     after_data pa ma (afterCopy pb mb machine sb db) sa da i inside,
     after_outside pb mb machine sb db (sa.add i) (readA i inside)]
  · have outsideA : ∀ i<ma.val,observer≠da.add i := by
     intro i inside equal
     exact hitA ⟨i,inside,equal⟩
    by_cases hitB : ∃ j,j<mb.val ∧ observer=db.add j
    · obtain ⟨j,inside,rfl⟩:=hitB
      rw [after_data pb mb (afterCopy pa ma machine sa da) sb db j inside,
       after_outside pa ma machine sa da (sb.add j) (readB j inside),
       after_outside pa ma (afterCopy pb mb machine sb db) sa da (db.add j) outsideA,
       after_data pb mb machine sb db j inside]
    · have outsideB : ∀ j<mb.val,observer≠db.add j := by
       intro j inside equal
       exact hitB ⟨j,inside,equal⟩
      rw [after_outside pb mb (afterCopy pa ma machine sa da) sb db observer outsideB,
       after_outside pa ma machine sa da observer outsideA,
       after_outside pa ma (afterCopy pb mb machine sb db) sa da observer outsideA,
       after_outside pb mb machine sb db observer outsideB]
 have stores := store_ext _ _ words
 exact congrArg (fun store : Evm.WordStore => {machine with store:=store}) stores

/-- Equality of actual intrinsic compiler instruction executions, including
all storage and context. This is not numeric-address or Source compilation. -/
theorem programs (pa pb : PrimTy) (ma mb : TypeGraph.FixedSize) (machine : Evm.Machine)
 (sa da sb db : Evm.Slot)
 (writes : ∀ i<ma.val,∀ j<mb.val,da.add i≠db.add j)
 (readA : ∀ i<ma.val,∀ j<mb.val,sa.add i≠db.add j)
 (readB : ∀ j<mb.val,∀ i<ma.val,sb.add j≠da.add i) :
 Evm.run (code pa ma sa da ++ code pb mb sb db) machine=
 Evm.run (code pb mb sb db ++ code pa ma sa da) machine := by
 rw [Evm.run_append_ok (run_code pa ma machine sa da),
  Evm.run_append_ok (run_code pb mb machine sb db),run_code,run_code]
 exact congrArg (fun result => Evm.Out.ok result 0) (machines pa pb ma mb machine sa da sb db writes readA readB)

/-- info: 'Solidity.Backend.StorageOps.TargetSnapshotCommutation.machines' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms machines
/-- info: 'Solidity.Backend.StorageOps.TargetSnapshotCommutation.programs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms programs
end Solidity.Backend.StorageOps.TargetSnapshotCommutation
