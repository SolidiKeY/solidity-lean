import Solidity.Backend.MemoryCopies.NestedMemoryPathInterface

/-! Existing selected pointer correctness chooses the actual source or rejects
its bounds. The existing nested copier checks capacity and supplies the same
original-heap snapshot adopted by the typed local binding. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

theorem SelectedAlias.nestedDeepExecute {C : Contract} {Γ : Ctx} {primitive : PrimTy} {L b frame : Nat} {frag : Frag Γ}
    {path : MPath C Γ (.ref (.array (.ref (.array (.prim primitive)))))} (chosen : SelectedAlias b frag path)
    (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine)
    (represented : Objects.StateRepr L b frame frag state base machine)
    (allocator : Objects.AllocatorRepr state.heap base frame cursor machine) (positive : 0 < b) :
    (∃ reference, path.mvalT state = .ok reference ∧ ∃ fits,
      NestedMemoryPathSuccess L b frame frag state base cursor machine reference chosen.nestedDeepCode fits) ∨
    NestedMemoryPathRefusal state cursor machine path chosen.nestedDeepCode := by
  rcases chosen.pointer.cert.correct represented with ⟨reference,resolved,pathRun⟩ | ⟨refused,pathRun⟩
  · rcases nested_memory_parent_correct state.heap primitive reference base frame cursor machine allocator with success | refusal
    · obtain ⟨fits,base',body,ran,allocated,root,extension,shape,below,gaps,keeps,fresh,length,newContents,oldContents⟩ := success
      let snapshot := MVal.copyMToSt state.heap (T := .ref (.array (.ref (.array (.prim primitive))))) reference
      let grown := snapshot.copyStToM state.heap rfl
      have adopted : Objects.StateRepr L b frame frag (state.adopt grown).1 base' body :=
        represented.adopt grown allocated.heap extension shape (fun address lower upper =>
          below address (by omega) (Nat.lt_of_lt_of_le upper (Nat.le_trans represented.locals allocator.free.above)))
      left
      refine ⟨reference,resolved,fits,base',body,?_,adopted,allocated,root,extension,shape,below,gaps,keeps,
        Nat.lt_of_lt_of_le reference.id_lt fresh,newContents,oldContents⟩
      rw [SelectedAlias.nestedDeepCode,run_append_ok pathRun]
      exact ran
    · right
      right
      refine ⟨reference,resolved,refusal.1,?_⟩
      rw [SelectedAlias.nestedDeepCode,run_append_ok pathRun]
      exact refusal.2
  · right
    left
    exact ⟨refused,run_append_revert pathRun⟩

theorem SelectedAlias.nestedDeepBindExecute {C : Contract} {Γ : Ctx} {primitive : PrimTy} {L b frame : Nat} {frag : Frag Γ}
    {path : MPath C Γ (.ref (.array (.ref (.array (.prim primitive)))))} (chosen : SelectedAlias b frag path)
    (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine)
    (destination : Idx Γ (.mem (.array (.ref (.array (.prim primitive))))))
    (represented : Objects.StateRepr L b frame frag state base machine)
    (allocator : Objects.AllocatorRepr state.heap base frame cursor machine) (positive : 0 < b) :
    (∃ reference, path.mvalT state = .ok reference ∧ ∃ fits,
      NestedMemoryPathBindSuccess L b frame frag state base cursor machine reference destination (chosen.nestedDeepBindCode destination) fits) ∨
    NestedMemoryPathRefusal state cursor machine path (chosen.nestedDeepBindCode destination) := by
  rcases chosen.nestedDeepExecute state base cursor machine represented allocator positive with success | refusal
  · obtain ⟨reference,resolved,fits,base',body,ran,adopted,allocated,root,extension,shape,below,gaps,keeps,fresh,newContents,oldContents⟩ := success
    let snapshot := MVal.copyMToSt state.heap (T := .ref (.array (.ref (.array (.prim primitive))))) reference
    let grown := snapshot.copyStToM state.heap rfl
    let target := writeMachine body (cellOf b destination) (.val cursor)
    left
    refine ⟨reference,resolved,fits,base',target,?_,?_,?_,root,extension,?_,?_,?_,keeps,fresh,newContents,oldContents⟩
    · rw [SelectedAlias.nestedDeepBindCode,run_append_ok ran]
      rfl
    · simpa only [snapshot,grown,root,target] using adopted.setMem destination grown.val
    · exact allocated.localWrite (lvl b destination) (Nat.lt_of_lt_of_le positive (le_lvl b destination))
        (Nat.lt_of_lt_of_le (lvl_lt b destination) represented.locals) (.val cursor)
    · change body.stack = machine.stack
      rw [shape]
    · exact upd_same _ _ _
    · intro address lower upper different
      change upd body.mem (cellOf b destination) (.val cursor) address = machine.mem address
      rw [upd_other _ _ different]
      exact below address lower upper
  · right
    rcases refusal with ⟨refused,failed⟩ | ⟨reference,resolved,tooLarge,failed⟩
    · exact .inl ⟨refused,run_append_revert failed⟩
    · exact .inr ⟨reference,resolved,tooLarge,run_append_revert failed⟩

def nestedMemoryPath : NestedMemoryPathCertificate :=
  ⟨SelectedAlias.nestedDeepExecute,SelectedAlias.nestedDeepBindExecute⟩

/--
info: 'Solidity.Backend.MemoryCopies.SelectedAlias.nestedDeepExecute' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SelectedAlias.nestedDeepExecute
/--
info: 'Solidity.Backend.MemoryCopies.SelectedAlias.nestedDeepBindExecute' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SelectedAlias.nestedDeepBindExecute
/--
info: 'Solidity.Backend.MemoryCopies.nestedMemoryPath' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms nestedMemoryPath
end Solidity.Backend.MemoryCopies
