import Solidity.Backend.StorageOps.PrimitiveSnapshotSelf

/-! Repetition of ACTUAL fixed snapshot compiler instructions. Self-copy or
generated source/write separation prevents a changed second capture.
No numeric-address/hash interpretation, Source lowering, gas or world claim. -/
namespace Solidity.Backend.StorageOps.TargetSnapshotRepeat
open TargetFixedSnapshot

private theorem store_ext (a b : Evm.WordStore) (same : ∀ s,a s=b s) : a=b := by
 cases a with
 | mk a =>
  cases b with
  | mk b =>
   have cells : a=b := funext (fun s => Fin.ext (same s))
   exact congrArg Evm.WordStore.mk cells

/-- Two ACTUAL copies have the first copy's entire Machine outcome when
source and destination coincide, or every generated source/write pair differs.
The separation premise is on actual slots, not a desired post-state equality. -/
theorem complete (p : PrimTy) (size : TypeGraph.FixedSize) (machine : Evm.Machine)
 (src dst : Evm.Slot)
 (safe : src=dst ∨ ∀ i<size.val,∀ j<size.val,src.add i≠dst.add j) :
 Evm.run (code p size src dst ++ code p size src dst) machine=
  .ok (afterCopy p size machine src dst) 0 ∧
 afterCopy p size (afterCopy p size machine src dst) src dst=afterCopy p size machine src dst := by
 have repeated : afterCopy p size (afterCopy p size machine src dst) src dst=afterCopy p size machine src dst := by
  rcases safe with same | separate
  · subst dst
    simp only [PrimitiveSnapshotSelf.machine_self]
  · classical
    have words : ∀ observer,
     (afterCopy p size (afterCopy p size machine src dst) src dst).store observer=
     (afterCopy p size machine src dst).store observer := by
      intro observer
      by_cases hit : ∃ i,i<size.val ∧ observer=dst.add i
      · obtain ⟨i,inside,rfl⟩:=hit
        rw [after_data p size (afterCopy p size machine src dst) src dst i inside,
         after_outside p size machine src dst (src.add i) (separate i inside),
         after_data p size machine src dst i inside]
      · apply after_outside
        intro i inside equal
        exact hit ⟨i,inside,equal⟩
    have stores := store_ext _ _ words
    exact congrArg (fun store : Evm.WordStore => {machine with store:=store}) stores
 refine ⟨?_,repeated⟩
 rw [Evm.run_append_ok (run_code p size machine src dst),run_code,repeated]

/-- info: 'Solidity.Backend.StorageOps.TargetSnapshotRepeat.complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms complete
end Solidity.Backend.StorageOps.TargetSnapshotRepeat
