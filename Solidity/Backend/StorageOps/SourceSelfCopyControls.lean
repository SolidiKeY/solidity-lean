import Solidity.Backend.StorageOps.TargetSelfCopy

/-! Populated target-only controls below the Source boundary. -/
namespace Solidity.Backend.StorageOps.SourceSelfCopyTargetControls

private def slot : Evm.Slot := .root 0
private def slots : List Evm.Slot := [slot,.data slot 0,.data (.data slot 0) 0,.data (.data slot 0) 1,
  .data slot 1,.data (.data slot 1) 0,.data slot 2,.data (.data slot 2) 0,.root 1,.root 9]
private def targetStore : Evm.WordStore := .ofFn fun s =>
  if s = slot then 2 else if s = .data slot 0 then 1 else if s = .data (.data slot 0) 0 then 7 else
  if s = .data (.data slot 0) 1 then 11 else if s = .data slot 1 then 1 else if s = .data (.data slot 1) 0 then 17 else
  if s = .data slot 2 then 1 else if s = .data (.data slot 2) 0 then 71 else if s = .root 9 then 99 else 0
private def tail : List Evm.Word := [.val ⟨23,by decide⟩,.slot (.root 9)]
private def machine : Evm.Machine :=
  { stack := tail, store := targetStore, mem := fun _ => .val ⟨31,by decide⟩,
    bal := fun _ => 37, bal₀ := fun _ => 41, self := ⟨43,by decide⟩,
    caller := ⟨47,by decide⟩, callvalue := ⟨0,by decide⟩, timestamp := ⟨53,by decide⟩,
    accepts := fun _ _ => false }
private def targetView (m : Evm.Machine) := slots.map (fun s => m.store s)
private def context (m : Evm.Machine) :=
  (m.stack,m.mem 0,m.bal ⟨0,by decide⟩,m.bal₀ ⟨0,by decide⟩,
   m.self,m.caller,m.callvalue,m.timestamp,m.accepts ⟨0,by decide⟩ ⟨0,by decide⟩)


theorem target_self :
    Evm.run TargetNestedArrayCopy.code { machine with stack := .slot slot :: .slot slot :: tail } = .ok machine 0 :=
  TargetSelfCopy.run_self machine tail slot

theorem target_ordered :
    (targetView machine,targetView (TargetNestedArrayRuntime.afterCopy machine tail slot slot),
      context (TargetNestedArrayRuntime.afterCopy machine tail slot slot)) =
    ([2,1,7,11,1,17,1,71,0,99],[2,1,7,11,1,17,1,71,0,99],context machine) := by
  rw [TargetSelfCopy.nested_after_self]
  rfl

/-- A different empty source clears the destination live prefix while preserving older shadows. -/
theorem different_target_ordered :
    (targetView (TargetNestedArrayRuntime.afterCopy machine tail (.root 1) slot),
      context (TargetNestedArrayRuntime.afterCopy machine tail (.root 1) slot)) =
    ([0,0,0,11,0,0,1,71,0,99],context machine) := by
  rfl

/-- info: 'Solidity.Backend.StorageOps.SourceSelfCopyTargetControls.target_self' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms target_self
/-- info: 'Solidity.Backend.StorageOps.SourceSelfCopyTargetControls.target_ordered' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms target_ordered
/-- info: 'Solidity.Backend.StorageOps.SourceSelfCopyTargetControls.different_target_ordered' does not depend on any axioms -/
#guard_msgs in #print axioms different_target_ordered
end Solidity.Backend.StorageOps.SourceSelfCopyTargetControls
