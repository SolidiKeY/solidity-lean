import Solidity.Backend.MemoryCopies.NestedMemoryPath
import Solidity.Backend.MemoryCopies.NestedMemoryPathFrameInterface

/-! Gap transport from the checked copy remains valid after the local store:
the store changes machine words, while object gaps depend on heap and base. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

theorem SelectedAlias.nestedDeepFramedBindExecute {C : Contract} {Γ : Ctx} {primitive : PrimTy} {L b frame : Nat} {frag : Frag Γ}
    {path : MPath C Γ (.ref (.array (.ref (.array (.prim primitive)))))} (chosen : SelectedAlias b frag path)
    (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine)
    (destination : Idx Γ (.mem (.array (.ref (.array (.prim primitive))))))
    (represented : Objects.StateRepr L b frame frag state base machine)
    (allocator : Objects.AllocatorRepr state.heap base frame cursor machine) (positive : 0 < b) :
    (∃ reference, path.mvalT state = .ok reference ∧ ∃ fits,
      NestedMemoryPathFramedBindSuccess L b frame frag state base cursor machine reference destination (chosen.nestedDeepBindCode destination) fits) ∨
    NestedMemoryPathRefusal state cursor machine path (chosen.nestedDeepBindCode destination) := by
  rcases chosen.nestedDeepExecute state base cursor machine represented allocator positive with success | refusal
  · obtain ⟨reference,resolved,fits,base',body,ran,adopted,allocated,root,extension,shape,below,gaps,keeps,fresh,newContents,oldContents⟩ := success
    let snapshot := MVal.copyMToSt state.heap (T := .ref (.array (.ref (.array (.prim primitive))))) reference
    let grown := snapshot.copyStToM state.heap rfl
    let target := writeMachine body (cellOf b destination) (.val cursor)
    left
    refine ⟨reference,resolved,fits,base',target,?_,?_,?_,root,extension,?_,?_,?_,gaps,keeps,fresh,newContents,oldContents⟩
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

def nestedMemoryPathFrame : NestedMemoryPathFrameCertificate :=
  ⟨SelectedAlias.nestedDeepFramedBindExecute⟩

/--
info: 'Solidity.Backend.MemoryCopies.SelectedAlias.nestedDeepFramedBindExecute' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SelectedAlias.nestedDeepFramedBindExecute
/--
info: 'Solidity.Backend.MemoryCopies.nestedMemoryPathFrame' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms nestedMemoryPathFrame

end Solidity.Backend.MemoryCopies
