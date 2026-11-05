import Solidity.Backend.StorageOps.TargetFixedSnapshot

/-! Actual captured target operands distinguish snapshot copy from streaming
in either overlap direction. No graph/source/numeric representation inferred. -/
namespace Solidity.Backend.StorageOps.TargetFixedSnapshot.Controls
private def size : TypeGraph.FixedSize := ⟨3,by decide⟩
private def slots : List Evm.Slot := [.root 0,.root 1,.root 2,.root 3,.root 4,.root 5]
private def target : Evm.Machine :=
 {Evm.Machine.init (fun _ => 19) ⟨7,by decide⟩ with
 store:=Evm.WordStore.ofFn (fun l => if l=.root 0 then 17 else if l=.root 1 then 23 else if l=.root 2 then 53 else if l=.root 3 then 71 else if l=.root 4 then 87 else if l=.root 5 then 99 else 0)
 stack:=[.val ⟨31,by decide⟩,.slot (.root 9)]
 mem:=fun _ => .val ⟨41,by decide⟩
 caller:=⟨13,by decide⟩
 timestamp:=⟨59,by decide⟩}
private def forward := afterCopy .uint size target (.root 0) (.root 1)
private def backward := afterCopy .uint size target (.root 1) (.root 0)
private def self := afterCopy .uint size target (.root 1) (.root 1)
private def words (machine : Evm.Machine) := slots.map (fun l => machine.store l)

theorem actual_copies : Evm.run (code .uint size (.root 0) (.root 1)) target=.ok forward 0 ∧
 Evm.run (code .uint size (.root 1) (.root 0)) target=.ok backward 0 ∧
 Evm.run (code .uint size (.root 1) (.root 1)) target=.ok self 0 := by
 exact ⟨run_code _ _ _ _ _,run_code _ _ _ _ _,run_code _ _ _ _ _⟩

theorem ordered : words target=[17,23,53,71,87,99] ∧ words forward=[17,17,23,53,87,99] ∧
 words backward=[23,53,71,71,87,99] ∧ words self=[17,23,53,71,87,99] ∧
 {forward with store:=target.store}=target ∧ {backward with store:=target.store}=target ∧
 {self with store:=target.store}=target := by
 exact ⟨by decide,by decide,by decide,by decide,rfl,rfl,rfl⟩

private def streamingForward := TargetOperations.copyCode (.root 1) (.root 0) ++
 (TargetOperations.copyCode (.root 2) (.root 1) ++ TargetOperations.copyCode (.root 3) (.root 2))
private def streamingBackward := TargetOperations.copyCode (.root 2) (.root 3) ++
 (TargetOperations.copyCode (.root 1) (.root 2) ++ TargetOperations.copyCode (.root 0) (.root 1))
private def forward1 : Evm.Machine := {target with store:=Evm.WordStore.write target.store (.root 1) 17}
private def forward2 : Evm.Machine := {forward1 with store:=Evm.WordStore.write forward1.store (.root 2) 17}
private def wrongForward : Evm.Machine := {forward2 with store:=Evm.WordStore.write forward2.store (.root 3) 17}
private def backward1 : Evm.Machine := {target with store:=Evm.WordStore.write target.store (.root 2) 71}
private def backward2 : Evm.Machine := {backward1 with store:=Evm.WordStore.write backward1.store (.root 1) 71}
private def wrongBackward : Evm.Machine := {backward2 with store:=Evm.WordStore.write backward2.store (.root 0) 71}
private theorem copy_known (machine : Evm.Machine) (dst src : Evm.Slot) (value : Nat)
 (known : machine.store src=value) :
 Evm.run (TargetOperations.copyCode dst src) machine=
 .ok {machine with store:=Evm.WordStore.write machine.store dst value} 0 := by
 rw [TargetOperations.run_copy,Evm.WordStore.cells_val,known]

/-- Wrong read/write interleaving is actual instruction execution, no oracle. -/
theorem wrong_interleaving :
 Evm.run streamingForward target=.ok wrongForward 0 ∧ Evm.run streamingBackward target=.ok wrongBackward 0 ∧
 words wrongForward=[17,17,17,17,87,99] ∧ words wrongBackward=[71,71,71,71,87,99] ∧
 wrongForward.store (.root 2)≠forward.store (.root 2) ∧ wrongBackward.store (.root 0)≠backward.store (.root 0) := by
 refine ⟨?_,?_,by decide,by decide,by decide,by decide⟩
 · unfold streamingForward
   rw [Evm.run_append_ok (copy_known target (.root 1) (.root 0) 17 rfl)]
   change Evm.run (TargetOperations.copyCode (.root 2) (.root 1) ++ TargetOperations.copyCode (.root 3) (.root 2)) forward1=.ok wrongForward 0
   rw [Evm.run_append_ok (copy_known forward1 (.root 2) (.root 1) 17
    (Evm.WordStore.write_same_of_lt _ _ _ (by decide)))]
   exact copy_known forward2 (.root 3) (.root 2) 17 (Evm.WordStore.write_same_of_lt _ _ _ (by decide))
 · unfold streamingBackward
   rw [Evm.run_append_ok (copy_known target (.root 2) (.root 3) 71 rfl)]
   change Evm.run (TargetOperations.copyCode (.root 1) (.root 2) ++ TargetOperations.copyCode (.root 0) (.root 1)) backward1=.ok wrongBackward 0
   rw [Evm.run_append_ok (copy_known backward1 (.root 1) (.root 2) 71
    (Evm.WordStore.write_same_of_lt _ _ _ (by decide)))]
   exact copy_known backward2 (.root 0) (.root 1) 71 (Evm.WordStore.write_same_of_lt _ _ _ (by decide))

private def captured : List Evm.Word := [.val ⟨71,by decide⟩,.val ⟨53,by decide⟩,.val ⟨23,by decide⟩]
private def processedStore := Evm.storeAt target.store (.root 0) [2] [71]
/-- Reverse prefix overwrites source cell2, yet remaining OLD53 is still an
actual stack operand. Continuation yields the snapshot, not reread71. -/
theorem captured_prefix :
 Evm.run (Evm.storeLeaves [2]) {target with stack:=.slot (.root 0)::(captured++target.stack)}=
 .ok {target with stack:=.slot (.root 0)::(.val ⟨53,by decide⟩:: .val ⟨23,by decide⟩::target.stack),store:=processedStore} 0 ∧
 processedStore (.root 2)=71 ∧ target.store (.root 2)=53 ∧
 Evm.run (Evm.storeLeaves [1,0] ++ [.pop])
 {target with stack:=.slot (.root 0)::(.val ⟨53,by decide⟩:: .val ⟨23,by decide⟩::target.stack),store:=processedStore}=.ok backward 0 := by
 refine ⟨?_,by decide,by decide,?_⟩
 · exact store_prefix .uint size target (.root 1) (.root 0) [2] [1,0] rfl
 · have rest := Evm.storeLeaves_run target (.root 0) [1,0] [⟨53,by decide⟩,⟨23,by decide⟩] target.stack processedStore
    (by intro o member; simp only [List.mem_cons,List.not_mem_nil,or_false] at member; rcases member with rfl|rfl <;> decide) rfl
   exact (Evm.run_append_ok rest).trans rfl

theorem reads :
 Evm.run (TargetOperations.readCode (.root 3)) forward=.ok {forward with stack:=.val ⟨53,by decide⟩::target.stack} 0 ∧
 Evm.run (TargetOperations.readCode (.root 0)) backward=.ok {backward with stack:=.val ⟨23,by decide⟩::target.stack} 0 := by
 exact ⟨rfl,rfl⟩

/-- info: 'Solidity.Backend.StorageOps.TargetFixedSnapshot.Controls.actual_copies' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms actual_copies
/-- info: 'Solidity.Backend.StorageOps.TargetFixedSnapshot.Controls.ordered' depends on axioms: [propext] -/
#guard_msgs in #print axioms ordered
/-- info: 'Solidity.Backend.StorageOps.TargetFixedSnapshot.Controls.wrong_interleaving' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms wrong_interleaving
/-- info: 'Solidity.Backend.StorageOps.TargetFixedSnapshot.Controls.captured_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms captured_prefix
/-- info: 'Solidity.Backend.StorageOps.TargetFixedSnapshot.Controls.reads' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms reads
end Solidity.Backend.StorageOps.TargetFixedSnapshot.Controls
