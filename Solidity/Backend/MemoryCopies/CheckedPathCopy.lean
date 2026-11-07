import Solidity.Backend.MemoryCopies.CheckedPathCopyInterface

/-! Existing pointer selection resolves or refuses; checked copying then
allocates or refuses capacity before adoption and the existing local store. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

theorem SelectedAlias.checkedDeepExecute {C : Contract} {Γ : Ctx} {primitive : PrimTy} {L b frame : Nat} {frag : Frag Γ}
    {path : MPath C Γ (.ref (.array (.prim primitive)))} (chosen : SelectedAlias b frag path)
    {state : State C Γ} {base : Nat → Fin W} {cursor : Fin W} {machine : Machine}
    (represented : Objects.StateRepr L b frame frag state base machine)
    (allocator : Objects.AllocatorRepr state.heap base frame cursor machine) (positive : 0 < b) :
    CheckedPathCopyOutcome L b frame frag state base cursor machine path chosen.checkedDeepCode := by
  rcases chosen.pointer.cert.correct represented with ⟨reference,resolved,pathRun⟩ | ⟨refused,pathRun⟩
  · by_cases fits : cursor.val + (state.heap.len reference .dyn + 1) < W
    · obtain ⟨base',body,ran,allocated,root,extension,shape,below,gaps,kept,fresh⟩ :=
        checked_memory_array_success state.heap primitive reference base frame cursor machine allocator fits
      let grown := (MVal.copyMToSt state.heap (T := .ref (.array (.prim primitive))) reference).copyStToM state.heap rfl
      have adopted : Objects.StateRepr L b frame frag (state.adopt grown).1 base' body :=
        represented.adopt grown allocated.heap extension shape (fun address lower upper =>
          below address (by omega) (Nat.lt_of_lt_of_le upper (Nat.le_trans represented.locals allocator.free.above)))
      refine .inl ⟨reference,resolved,fits,base',body,?_,adopted,allocated,root,extension,shape,below,gaps,kept,fresh⟩
      rw [SelectedAlias.checkedDeepCode,run_append_ok pathRun]
      exact ran
    · right
      refine ⟨Or.inr ⟨reference,resolved,fits⟩,?_⟩
      rw [SelectedAlias.checkedDeepCode,run_append_ok pathRun,
        checked_memory_array_run state.heap primitive reference base frame cursor machine allocator,if_neg fits]
  · exact .inr ⟨Or.inl refused,run_append_revert pathRun⟩

theorem SelectedAlias.checkedDeepBindExecute {C : Contract} {Γ : Ctx} {primitive : PrimTy} {L b frame : Nat} {frag : Frag Γ}
    {path : MPath C Γ (.ref (.array (.prim primitive)))} (chosen : SelectedAlias b frag path)
    {state : State C Γ} {base : Nat → Fin W} {cursor : Fin W} {machine : Machine}
    (represented : Objects.StateRepr L b frame frag state base machine)
    (allocator : Objects.AllocatorRepr state.heap base frame cursor machine) (positive : 0 < b)
    (destination : Idx Γ (.mem (.array (.prim primitive)))) :
    CheckedPathBindOutcome L b frame frag state base cursor machine path destination (chosen.checkedDeepBindCode destination) := by
  rcases chosen.checkedDeepExecute represented allocator positive with
    ⟨reference,resolved,fits,base',body,ran,adopted,allocated,root,extension,shape,below,_,kept,fresh⟩ | ⟨refused,failed⟩
  · let grown := (MVal.copyMToSt state.heap (T := .ref (.array (.prim primitive))) reference).copyStToM state.heap rfl
    let target := writeMachine body (cellOf b destination) (.val cursor)
    refine .inl ⟨reference,resolved,fits,base',target,?_,?_,?_,root,extension,?_,?_,?_,kept,fresh⟩
    · rw [SelectedAlias.checkedDeepBindCode,run_append_ok ran]
      rfl
    · simpa only [grown,root,target] using adopted.setMem destination grown.val
    · exact allocated.localWrite (lvl b destination) (Nat.lt_of_lt_of_le positive (le_lvl b destination))
        (Nat.lt_of_lt_of_le (lvl_lt b destination) represented.locals) (.val cursor)
    · change body.stack = machine.stack
      rw [shape]
    · exact upd_same _ _ _
    · intro address lower upper different
      change upd body.mem (cellOf b destination) (.val cursor) address = machine.mem address
      rw [upd_other _ _ different]
      exact below address lower upper
  · exact .inr ⟨refused,run_append_revert failed⟩

def checkedPathCopy : CheckedPathCopyCertificate := ⟨SelectedAlias.checkedDeepExecute,SelectedAlias.checkedDeepBindExecute⟩

#print axioms SelectedAlias.checkedDeepExecute
#print axioms SelectedAlias.checkedDeepBindExecute
#print axioms checkedPathCopy
end Solidity.Backend.MemoryCopies
