import Solidity.Backend.StorageOps.PrimitiveCycleMachine

/-! Whole-machine primitive cycle controls: all runtime headers, full-word
boundary, complete ordered target views, dirty-child negative and context.
No numeric hash interpretation or independent ordinary Source/world claim. -/
namespace Solidity.Backend.StorageOps.PrimitiveCycleMachine.Controls
private def root : Evm.Slot := .root 0
private def child (i : Nat) : Evm.Slot := .data root i
private def opaqueSlot : Evm.Slot := .hash ⟨7,by decide⟩ (child 1) 0
private def target (length : Fin Evm.W) : Evm.Machine :=
 {stack := [.val ⟨23,by decide⟩,.slot (.root 9)],
  store := .ofFn fun s => if s=root then length.val else if s=child 3 then 99 else if s=opaqueSlot then 77 else 53,
  mem := fun _ => .val ⟨31,by decide⟩,bal := fun _ => 19,bal₀ := fun _ => 19,
  self := ⟨7,by decide⟩,caller := ⟨13,by decide⟩,callvalue := ⟨11,by decide⟩,
  timestamp := ⟨53,by decide⟩,accepts := fun _ _ => false}
private def small (i : Fin 4) : Fin Evm.W := ⟨i.val,by have h:=i.isLt; unfold Evm.W; omega⟩
private theorem header (length : Fin Evm.W) : (target length).store root=length.val := by
 change length.val % Evm.W=length.val
 exact Nat.mod_eq_of_lt length.isLt
private def slots := [root,child 0,child 1,child 2,child 3,opaqueSlot,.root 9,child 1]
private def view (m : Evm.Machine) := slots.map (fun s => m.store s)
private def observe : Evm.Out → Option (List Nat)
 | .ok m _ => some (view m)
 | _ => none
private def context (m : Evm.Machine) := (m.stack,m.mem 0,m.bal m.self,m.bal₀ m.self,m.self,m.caller,m.callvalue,m.timestamp,m.accepts m.self m.self)

/-- All positive runtime word lengths, not a finite enumeration or lmax cap;
actual execution and selected clear plus EVERY outside-slot frame. -/
theorem arbitrary_headers (length : Fin Evm.W) (positive : 0<length.val) :
 Evm.run (PrimitiveCycleProgram.code root) (target length)=.ok (afterPop (target length) root) 0 ∧
 (afterPop (target length) root).store root=length.val-1 ∧
 (afterPop (target length) root).store (child (length.val-1))=0 ∧
 ∀ s, s ≠ root → s ≠ child (length.val-1) →
 (afterPop (target length) root).store s=(target length).store s := by
 refine ⟨?_,?_,?_,?_⟩
 · rw [run_cycle,header,if_neg (by omega)]
 · rw [(pop_observations _ _).1,header]
 · have clear := (pop_observations (target length) root).2
   rw [header] at clear
   exact clear
 · intro s notRoot notChild
   unfold afterPop
   rw [header]
   change Evm.WordStore.write (Evm.WordStore.write (target length).store root (length.val-1)) (child (length.val-1)) 0 s=(target length).store s
   rw [Evm.WordStore.write_other _ _ notChild,Evm.WordStore.write_other _ _ notRoot]

/-- Complete ordered ACTUAL execution outcomes at empty/one/two/three runtime
lengths. Mapping-like opaqueSlot77, older99, outside53 and repeated query retained. -/
theorem ordered :
 ([small 0,small 1,small 2,small 3].map (fun h => observe (Evm.run (PrimitiveCycleProgram.code root) (target h)))) =
 [none,some [0,0,53,53,99,77,53,53],some [1,53,0,53,99,77,53,0],some [2,53,53,0,99,77,53,53]] := by
 simp only [List.map_cons,List.map_nil,run_cycle]
 rfl

/-- Entire non-store context preserved, including nonempty stack, memory,
balances and environment. The core law is whole-Machine equality. -/
theorem context_preserved (length : Fin Evm.W) :
 context (afterPop (target length) root)=context (target length) := rfl

private def high : Fin Evm.W := ⟨Evm.W-1,by have h:=Evm.W_pos; omega⟩
/-- Maximum runtime word header is inhabited, with no legacy metadata premise.
Initial pop derives room for push; final header is W-2, not an overflow. -/
theorem fullword : Evm.run (PrimitiveCycleProgram.code root) (target high)=.ok (afterPop (target high) root) 0 ∧
 (afterPop (target high) root).store root=Evm.W-2 ∧
 (afterPop (target high) root).store (child (Evm.W-2))=0 := by
 have positive : 0<high.val := by change 0<Evm.W-1; unfold Evm.W; decide
 have actual := arbitrary_headers high positive
 refine ⟨actual.1,?_,?_⟩
 · have h:=actual.2.1
   change _=Evm.W-1-1 at h
   exact h.trans (by omega)
 · have h : (afterPop (target high) root).store (child (Evm.W-1-1))=0 := actual.2.2.1
   simpa only [Nat.sub_sub] using h

private def dirty := target (small 2)
private def wrong := afterPop (afterPush dirty root) root
/-- Dropping zero-reuse premise is false: actual push/pop clears dirty older
payload53, preserves header2 and all other observations, and changes Machine. -/
theorem dirty_negative :
 Evm.run (TargetPrimitivePush.code root ++ TargetPrimitivePop.code root) dirty=.ok wrong 0 ∧
 (view dirty,view wrong)=([2,53,53,53,99,77,53,53],[2,53,53,0,99,77,53,53]) ∧
 wrong ≠ dirty := by
 refine ⟨?_,rfl,?_⟩
 · rw [Evm.run_append_ok (m' := afterPush dirty root) (by rw [TargetPrimitivePush.run_current]; rfl),TargetPrimitivePop.run_current]
   rfl
 · intro same
   have bad:=congrArg (fun m : Evm.Machine => m.store (child 2)) same
   change (0:Nat)=53 at bad
   omega

/-- info: 'Solidity.Backend.StorageOps.PrimitiveCycleMachine.Controls.arbitrary_headers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms arbitrary_headers
/-- info: 'Solidity.Backend.StorageOps.PrimitiveCycleMachine.Controls.ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ordered
/-- info: 'Solidity.Backend.StorageOps.PrimitiveCycleMachine.Controls.context_preserved' does not depend on any axioms -/
#guard_msgs in #print axioms context_preserved
/-- info: 'Solidity.Backend.StorageOps.PrimitiveCycleMachine.Controls.fullword' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms fullword
/-- info: 'Solidity.Backend.StorageOps.PrimitiveCycleMachine.Controls.dirty_negative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms dirty_negative
end Solidity.Backend.StorageOps.PrimitiveCycleMachine.Controls
