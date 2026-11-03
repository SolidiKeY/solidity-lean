import Solidity.Backend.StorageOps.TargetSnapshotRepeat

/-! Actual instruction runs, full ordered storage views and full context frames.
Overlap controls distinguish a second CURRENT capture from a frozen source.
No numeric-address, ordinary Source, external EVM, gas or world conclusion. -/
namespace Solidity.Backend.StorageOps.TargetSnapshotRepeatControls
open TargetFixedSnapshot
private def size : TypeGraph.FixedSize := ⟨3,by decide⟩
private def slots : List Evm.Slot := [.root 0,.root 1,.root 2,.root 3,.root 4,.root 5,.root 6,.root 7,.root 8]
private def target : Evm.Machine :=
 {Evm.Machine.init (fun _ => 19) ⟨7,by decide⟩ with
 store:=Evm.WordStore.ofFn (fun l => if l=.root 0 then 17 else if l=.root 1 then 23 else if l=.root 2 then 53 else if l=.root 3 then 71 else if l=.root 4 then 87 else if l=.root 5 then 99 else if l=.root 6 then 101 else if l=.root 7 then 109 else if l=.root 8 then 127 else 0)
 stack:=[.val ⟨31,by decide⟩,.slot (.root 9)]
 mem:=fun _ => .val ⟨41,by decide⟩
 caller:=⟨13,by decide⟩
 timestamp:=⟨59,by decide⟩}
private def words (machine : Evm.Machine) := slots.map (fun l => machine.store l)
private def separate (machine : Evm.Machine) := afterCopy .uint size machine (.root 0) (.root 4)
private def separateCode := code .uint size (.root 0) (.root 4)
private def selfCode := code .uint size (.root 0) (.root 0)
private def right (machine : Evm.Machine) := afterCopy .uint size machine (.root 0) (.root 1)
private def rightCode := code .uint size (.root 0) (.root 1)
private def left (machine : Evm.Machine) := afterCopy .uint size machine (.root 1) (.root 0)
private def leftCode := code .uint size (.root 1) (.root 0)
private theorem separated : ∀ i<size.val,∀ j<size.val,(Evm.Slot.root 0).add i≠(Evm.Slot.root 4).add j := by
 decide

/-- Nonempty genuine client of the generated-slot separation premise. -/
theorem separated_certificate :
 Evm.run (separateCode++separateCode) target=.ok (separate target) 0 ∧
 separate (separate target)=separate target := by
 exact TargetSnapshotRepeat.complete .uint size target (.root 0) (.root 4) (Or.inr separated)

/-- Complete OLD/once/twice nine-word vectors, including unchanged older words. -/
theorem separated_ordered :
 (words target,words (separate target),words (separate (separate target)))=
 ([17,23,53,71,87,99,101,109,127],
  [17,23,53,71,17,23,53,109,127],
  [17,23,53,71,17,23,53,109,127]) ∧
 Evm.run separateCode target=.ok (separate target) 0 := by
 exact ⟨by decide,run_code _ _ _ _ _⟩

/-- Same-slot copying takes the other branch and preserves the WHOLE machine. -/
theorem self_certificate : Evm.run (selfCode++selfCode) target=.ok target 0 ∧
 afterCopy .uint size (afterCopy .uint size target (.root 0) (.root 0)) (.root 0) (.root 0)=target := by
 simpa only [PrimitiveSnapshotSelf.machine_self] using
  TargetSnapshotRepeat.complete .uint size target (.root 0) (.root 0) (Or.inl rfl)

/-- Each overlapping run is still a real snapshot; the second capture differs. -/
theorem right_overlap :
 Evm.run rightCode target=.ok (right target) 0 ∧
 Evm.run (rightCode++rightCode) target=.ok (right (right target)) 0 ∧
 (words (right target),words (right (right target)))=
 ([17,17,23,53,87,99,101,109,127],[17,17,17,23,87,99,101,109,127]) := by
 refine ⟨run_code _ _ _ _ _,?_,by decide⟩
 simp only [rightCode]
 rw [Evm.run_append_ok (run_code .uint size target (.root 0) (.root 1)),run_code]
 rfl

/-- Opposite overlap direction also changes between first and second runs. -/
theorem left_overlap :
 Evm.run leftCode target=.ok (left target) 0 ∧
 Evm.run (leftCode++leftCode) target=.ok (left (left target)) 0 ∧
 (words (left target),words (left (left target)))=
 ([23,53,71,71,87,99,101,109,127],[53,71,71,71,87,99,101,109,127]) := by
 refine ⟨run_code _ _ _ _ _,?_,by decide⟩
 simp only [leftCode]
 rw [Evm.run_append_ok (run_code .uint size target (.root 1) (.root 0)),run_code]
 rfl

/-- The real overlap cases violate the premise and refute unrestricted repetition. -/
theorem overlap_refutes :
 ¬((Evm.Slot.root 0)=.root 1 ∨ ∀ i<size.val,∀ j<size.val,(Evm.Slot.root 0).add i≠(Evm.Slot.root 1).add j) ∧
 ¬((Evm.Slot.root 1)=.root 0 ∨ ∀ i<size.val,∀ j<size.val,(Evm.Slot.root 1).add i≠(Evm.Slot.root 0).add j) ∧
 (right (right target)).store (.root 2)≠(right target).store (.root 2) ∧
 (left (left target)).store (.root 0)≠(left target).store (.root 0) := by
 exact ⟨by decide,by decide,by decide,by decide⟩

/-- All nonstore fields, including function-valued memory/balances, are exact. -/
theorem whole_context :
 {separate target with store:=target.store}=target ∧
 {separate (separate target) with store:=target.store}=target ∧
 {right target with store:=target.store}=target ∧
 {right (right target) with store:=target.store}=target ∧
 {left target with store:=target.store}=target ∧
 {left (left target) with store:=target.store}=target := by
 exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- First-run OLD captures and second-run CURRENT captures are both observable. -/
theorem source_captures :
 (target.store (.root 1),(right target).store (.root 1),
  (right target).store (.root 2),(right (right target)).store (.root 2),
  target.store (.root 1),(left target).store (.root 1),
  (left target).store (.root 0),(left (left target)).store (.root 0),
  (separate target).store (.root 0),(separate target).store (.root 1),(separate target).store (.root 2))=
 (23,17,23,17,23,53,23,53,17,23,53) := by rfl

/-- info: 'Solidity.Backend.StorageOps.TargetSnapshotRepeatControls.separated_certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms separated_certificate
/-- info: 'Solidity.Backend.StorageOps.TargetSnapshotRepeatControls.separated_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms separated_ordered
/-- info: 'Solidity.Backend.StorageOps.TargetSnapshotRepeatControls.self_certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms self_certificate
/-- info: 'Solidity.Backend.StorageOps.TargetSnapshotRepeatControls.right_overlap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms right_overlap
/-- info: 'Solidity.Backend.StorageOps.TargetSnapshotRepeatControls.left_overlap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms left_overlap
/-- info: 'Solidity.Backend.StorageOps.TargetSnapshotRepeatControls.overlap_refutes' depends on axioms: [propext] -/
#guard_msgs in #print axioms overlap_refutes
/-- info: 'Solidity.Backend.StorageOps.TargetSnapshotRepeatControls.whole_context' depends on axioms: [propext] -/
#guard_msgs in #print axioms whole_context
/-- info: 'Solidity.Backend.StorageOps.TargetSnapshotRepeatControls.source_captures' depends on axioms: [propext] -/
#guard_msgs in #print axioms source_captures
end Solidity.Backend.StorageOps.TargetSnapshotRepeatControls
