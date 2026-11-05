import Solidity.Backend.StorageOps.TargetSnapshotCommutation

/-! Actual two-program controls. Each operation may overlap its own source;
cross-operation dependencies and destination collisions remain observable. -/
namespace Solidity.Backend.StorageOps.TargetSnapshotCommutation.Controls
open TargetFixedSnapshot
private def ma : TypeGraph.FixedSize := ⟨2,by decide⟩
private def mb : TypeGraph.FixedSize := ⟨3,by decide⟩
private def slots : List Evm.Slot := [.root 0,.root 1,.root 2,.root 3,.root 4,.root 5,.root 6,.root 7,.root 8]
private def target : Evm.Machine :=
 {Evm.Machine.init (fun _ => 19) ⟨7,by decide⟩ with
 store:=Evm.WordStore.ofFn (fun l => if l=.root 0 then 17 else if l=.root 1 then 23 else if l=.root 2 then 53 else if l=.root 3 then 71 else if l=.root 4 then 87 else if l=.root 5 then 99 else if l=.root 6 then 101 else if l=.root 7 then 109 else if l=.root 8 then 127 else 0)
 stack:=[.val ⟨31,by decide⟩,.slot (.root 9)]
 mem:=fun _ => .val ⟨41,by decide⟩
 caller:=⟨13,by decide⟩
 timestamp:=⟨59,by decide⟩}
private def words (machine : Evm.Machine) := slots.map (fun l => machine.store l)
private def a (machine : Evm.Machine) := afterCopy .uint ma machine (.root 0) (.root 1)
private def b (machine : Evm.Machine) := afterCopy .uint mb machine (.root 4) (.root 5)
private def ca := code .uint ma (.root 0) (.root 1)
private def cb := code .uint mb (.root 4) (.root 5)
private theorem writes : ∀ i<ma.val,∀ j<mb.val,(Evm.Slot.root 1).add i≠(Evm.Slot.root 5).add j := by
 intro i hi j hj same
 change Evm.Slot.root (1+i)=.root (5+j) at same
 have equal:=Evm.Slot.root.inj same
 change i<2 at hi
 change j<3 at hj
 omega
private theorem readA : ∀ i<ma.val,∀ j<mb.val,(Evm.Slot.root 0).add i≠(Evm.Slot.root 5).add j := by
 intro i hi j hj same
 change Evm.Slot.root (0+i)=.root (5+j) at same
 have equal:=Evm.Slot.root.inj same
 change i<2 at hi
 change j<3 at hj
 omega
private theorem readB : ∀ j<mb.val,∀ i<ma.val,(Evm.Slot.root 4).add j≠(Evm.Slot.root 1).add i := by
 intro j hj i hi same
 change Evm.Slot.root (4+j)=.root (1+i) at same
 have equal:=Evm.Slot.root.inj same
 change i<2 at hi
 change j<3 at hj
 omega
private theorem run_two (pa pb : PrimTy) (x y : TypeGraph.FixedSize) (machine : Evm.Machine) (sa da sb db : Evm.Slot) :
 Evm.run (code pa x sa da ++ code pb y sb db) machine=
 .ok (afterCopy pb y (afterCopy pa x machine sa da) sb db) 0 := by
 rw [Evm.run_append_ok (run_code pa x machine sa da),run_code]

theorem certificate : b (a target)=a (b target) ∧ Evm.run (ca++cb) target=Evm.run (cb++ca) target := by
 exact ⟨machines .uint .uint ma mb target (.root 0) (.root 1) (.root 4) (.root 5) writes readA readB,
  programs .uint .uint ma mb target (.root 0) (.root 1) (.root 4) (.root 5) writes readA readB⟩

theorem actual_sequences : Evm.run ca target=.ok (a target) 0 ∧ Evm.run cb target=.ok (b target) 0 ∧
 Evm.run (ca++cb) target=.ok (b (a target)) 0 ∧ Evm.run (cb++ca) target=.ok (a (b target)) 0 := by
 exact ⟨run_code _ _ _ _ _,run_code _ _ _ _ _,run_two _ _ _ _ _ _ _ _ _,run_two _ _ _ _ _ _ _ _ _⟩

theorem ordered : words target=[17,23,53,71,87,99,101,109,127] ∧
 words (a target)=[17,17,23,71,87,99,101,109,127] ∧
 words (b target)=[17,23,53,71,87,87,99,101,127] ∧
 words (b (a target))=[17,17,23,71,87,87,99,101,127] ∧
 words (a (b target))=[17,17,23,71,87,87,99,101,127] ∧
 {a target with store:=target.store}=target ∧ {b target with store:=target.store}=target ∧
 {b (a target) with store:=target.store}=target ∧ {a (b target) with store:=target.store}=target := by
 exact ⟨by decide,by decide,by decide,by decide,by decide,rfl,rfl,rfl,rfl⟩

theorem captured_operands : target.store (.root 1)=23 ∧ (a target).store (.root 1)=17 ∧
 (b (a target)).store (.root 2)=23 ∧ target.store (.root 5)=99 ∧ (b target).store (.root 5)=87 ∧
 (a (b target)).store (.root 6)=99 := by
 exact ⟨by decide,by decide,by decide,by decide,by decide,by decide⟩

private def dependent (machine : Evm.Machine) := afterCopy .uint mb machine (.root 1) (.root 5)
private def dependentCode := code .uint mb (.root 1) (.root 5)
theorem read_dependency_negative :
 (∀ i<ma.val,∀ j<mb.val,(Evm.Slot.root 1).add i≠(Evm.Slot.root 5).add j) ∧
 (∀ i<ma.val,∀ j<mb.val,(Evm.Slot.root 0).add i≠(Evm.Slot.root 5).add j) ∧
 ¬(∀ j<mb.val,∀ i<ma.val,(Evm.Slot.root 1).add j≠(Evm.Slot.root 1).add i) ∧
 Evm.run (ca++dependentCode) target=.ok (dependent (a target)) 0 ∧
 Evm.run (dependentCode++ca) target=.ok (a (dependent target)) 0 ∧
 words (dependent (a target))=[17,17,23,71,87,17,23,71,127] ∧
 words (a (dependent target))=[17,17,23,71,87,23,53,71,127] ∧
 (dependent (a target)).store (.root 5)≠(a (dependent target)).store (.root 5) := by
 refine ⟨writes,readA,?_,run_two _ _ _ _ _ _ _ _ _,run_two _ _ _ _ _ _ _ _ _,by decide,by decide,by decide⟩
 intro separated
 exact separated 0 (by decide) 0 (by decide) rfl

private def colliding (machine : Evm.Machine) := afterCopy .uint mb machine (.root 4) (.root 2)
private def collidingCode := code .uint mb (.root 4) (.root 2)
theorem write_collision_negative :
 (∀ i<ma.val,∀ j<mb.val,(Evm.Slot.root 0).add i≠(Evm.Slot.root 2).add j) ∧
 (∀ j<mb.val,∀ i<ma.val,(Evm.Slot.root 4).add j≠(Evm.Slot.root 1).add i) ∧
 ¬(∀ i<ma.val,∀ j<mb.val,(Evm.Slot.root 1).add i≠(Evm.Slot.root 2).add j) ∧
 Evm.run (ca++collidingCode) target=.ok (colliding (a target)) 0 ∧
 Evm.run (collidingCode++ca) target=.ok (a (colliding target)) 0 ∧
 words (colliding (a target))=[17,17,87,99,101,99,101,109,127] ∧
 words (a (colliding target))=[17,17,23,99,101,99,101,109,127] ∧
 (colliding (a target)).store (.root 2)≠(a (colliding target)).store (.root 2) := by
 refine ⟨?_,readB,?_,run_two _ _ _ _ _ _ _ _ _,run_two _ _ _ _ _ _ _ _ _,by decide,by decide,by decide⟩
 · intro i hi j hj same
   change Evm.Slot.root (0+i)=.root (2+j) at same
   have equal:=Evm.Slot.root.inj same
   change i<2 at hi
   change j<3 at hj
   omega
 · intro separated
   exact separated 1 (by decide) 0 (by decide) rfl

/-- info: 'Solidity.Backend.StorageOps.TargetSnapshotCommutation.Controls.certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms certificate
/-- info: 'Solidity.Backend.StorageOps.TargetSnapshotCommutation.Controls.actual_sequences' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms actual_sequences
/-- info: 'Solidity.Backend.StorageOps.TargetSnapshotCommutation.Controls.ordered' depends on axioms: [propext] -/
#guard_msgs in #print axioms ordered
/-- info: 'Solidity.Backend.StorageOps.TargetSnapshotCommutation.Controls.captured_operands' depends on axioms: [propext] -/
#guard_msgs in #print axioms captured_operands
/-- info: 'Solidity.Backend.StorageOps.TargetSnapshotCommutation.Controls.read_dependency_negative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms read_dependency_negative
/-- info: 'Solidity.Backend.StorageOps.TargetSnapshotCommutation.Controls.write_collision_negative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms write_collision_negative
end Solidity.Backend.StorageOps.TargetSnapshotCommutation.Controls
