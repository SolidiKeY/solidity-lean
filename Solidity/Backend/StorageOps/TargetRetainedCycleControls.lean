import Solidity.Backend.StorageOps.TargetRetainedCycle

/-! Inhabited actual target cycle controls. This fixture does not invent an
ordinary Source push/pop evaluator or numeric representation premise. -/
namespace Solidity.Backend.StorageOps.TargetRetainedCycle.Controls
private def outer : Evm.Slot := .root 0
private def child (i : Nat) : Evm.Slot := .data outer i
private def cell (i j : Nat) : Evm.Slot := .data (child i) j
private def rawOpaque : Evm.Slot := .hash ⟨7,by decide⟩ (child 2) 0
private def store : Evm.WordStore := .ofFn fun s =>
 if s=outer then 3 else if s=child 0 then 3 else if s=child 1 then 0 else if s=child 2 then 2 else if s=child 3 then 1 else
 if s=cell 0 0 then 7 else if s=cell 0 1 then 17 else if s=cell 0 2 then 23 else if s=cell 0 3 then 71 else
 if s=cell 1 0 then 83 else if s=cell 2 0 then 53 else if s=cell 2 1 then 59 else if s=cell 2 2 then 61 else
 if s=cell 3 0 then 79 else if s=cell 3 1 then 89 else if s=rawOpaque then 77 else if s=.root 9 then 99 else 87
private def tail : List Evm.Word := [.val ⟨23,by decide⟩,.slot (.root 9)]
private def target : Evm.Machine :=
 {stack := tail,store := store,mem := fun _ => .val ⟨31,by decide⟩,
  bal := fun _ => 19,bal₀ := fun _ => 19,self := ⟨7,by decide⟩,caller := ⟨13,by decide⟩,
  callvalue := ⟨0,by decide⟩,timestamp := ⟨53,by decide⟩,accepts := fun _ _ => false}
private def out1 := TargetNestedPop.after target outer
private def out2 := TargetNestedPop.after out1 outer
private def out3 := TargetNestedPop.after out2 outer
private def slots := [outer,child 0,child 1,child 2,child 3,cell 0 0,cell 0 1,cell 0 2,cell 0 3,
 cell 1 0,cell 2 0,cell 2 1,cell 2 2,cell 3 0,cell 3 1,rawOpaque,.root 9,.root 77]
private def view (m : Evm.Machine) := slots.map (fun s => m.store s)
private def contextView (m : Evm.Machine) :=
 (m.stack,m.mem 0,m.bal m.self,m.bal₀ m.self,m.self,m.caller,m.callvalue,m.timestamp,m.accepts m.self m.self)

private def grown := TargetHeaderPush.incremented outer out1

theorem executions : Evm.run (popRegrowPop outer) target = .ok out1 0 ∧
 Evm.run (code outer) out1 = .ok out1 0 ∧
 Evm.run (code outer ++ code outer) out1 = .ok out1 0 := by
 refine ⟨(run_pop_regrow_pop target outer).trans (by rfl),?_,?_⟩
 · exact run_reuse out1 outer (by decide) rfl
 · exact (Evm.run_append_ok (run_reuse out1 outer (by decide) rfl)).trans (run_reuse out1 outer (by decide) rfl)

/-- Every observed word/context of the reused cleared child, other live/empty
children, older shadow, opaque mapping-like cell and outside slots is pinned. -/
theorem ordered : (view target,view out1,view grown,view (TargetNestedPop.after grown outer),
 contextView out1,contextView grown,contextView (TargetNestedPop.after grown outer)) =
 ([3,3,0,2,1,7,17,23,71,83,53,59,61,79,89,77,99,87],
  [2,3,0,0,1,7,17,23,71,83,0,0,61,79,89,77,99,87],
  [3,3,0,0,1,7,17,23,71,83,0,0,61,79,89,77,99,87],
  [2,3,0,0,1,7,17,23,71,83,0,0,61,79,89,77,99,87],
  contextView target,contextView target,contextView target) := by rfl

private def wrong := TargetNestedPop.after (TargetHeaderPush.incremented outer target) outer
/-- Omitting the cleared-child premise is false: an actual push/pop on OLD
state selects the older nonempty child, clearing79 but preserving53 and59. -/
theorem uncleared_negative : Evm.run (code outer) target = .ok wrong 0 ∧
 view wrong = [3,3,0,2,0,7,17,23,71,83,53,59,61,0,89,77,99,87] ∧ wrong ≠ target := by
 constructor
 · unfold code
   rw [Evm.run_append_ok (m' := TargetHeaderPush.incremented outer target)
     (by rw [TargetHeaderPush.run_current]; rfl),TargetNestedPop.run_current]
   rfl
 refine ⟨rfl,?_⟩
 intro same
 have observed := congrArg (fun m : Evm.Machine => m.store (cell 3 0)) same
 change (0 : Nat) = 79 at observed
 omega

private def full : Evm.Machine := {out1 with store := Evm.WordStore.write out1.store outer (Evm.W-1)}
private def empty : Evm.Machine := {target with store := Evm.WordStore.write target.store outer 0}
theorem failures : Evm.run (code outer) full = .revert ∧
 Evm.run (popRegrowPop outer) empty = .revert := by
 constructor
 · unfold code
   apply Evm.run_append_revert
   rw [TargetHeaderPush.run_current]
   rfl
 · rw [run_pop_regrow_pop]
   rfl

/-- Distinguish stability from restoring original live payload. -/
theorem changed_payload : out1.store (cell 2 0) = 0 ∧ target.store (cell 2 0) = 53 ∧
 out1.store (cell 2 2) = 61 ∧ out1.store (cell 3 0) = 79 ∧ out1 ≠ target := by
 refine ⟨rfl,rfl,rfl,rfl,?_⟩
 intro same
 have observed := congrArg (fun m : Evm.Machine => m.store (cell 2 0)) same
 change (0 : Nat) = 53 at observed
 omega

/-- info: 'Solidity.Backend.StorageOps.TargetRetainedCycle.Controls.executions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms executions
/-- info: 'Solidity.Backend.StorageOps.TargetRetainedCycle.Controls.ordered' does not depend on any axioms -/
#guard_msgs in #print axioms ordered
/-- info: 'Solidity.Backend.StorageOps.TargetRetainedCycle.Controls.uncleared_negative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms uncleared_negative
/-- info: 'Solidity.Backend.StorageOps.TargetRetainedCycle.Controls.failures' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms failures
/-- info: 'Solidity.Backend.StorageOps.TargetRetainedCycle.Controls.changed_payload' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms changed_payload
end Solidity.Backend.StorageOps.TargetRetainedCycle.Controls
