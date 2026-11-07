import Solidity.Backend.MemoryCopies.CheckedFixedPathCopyInterface

/-! Existing pointer selection resolves or refuses; checked copying then
allocates or refuses capacity before adoption and the existing local store. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

theorem SelectedAlias.checkedFixedDeepExecute {C : Contract} {Γ : Ctx} {primitive : PrimTy} {count : Nat} {L b frame : Nat} {frag : Frag Γ}
    {path : MPath C Γ (.ref (.fixed (.prim primitive) count))} (chosen : SelectedAlias b frag path)
    {state : State C Γ} {base : Nat → Fin W} {cursor : Fin W} {machine : Machine}
    (represented : Objects.StateRepr L b frame frag state base machine)
    (allocator : Objects.AllocatorRepr state.heap base frame cursor machine) (positive : 0 < b) :
    CheckedFixedPathCopyOutcome L b frame frag state base cursor machine path chosen.checkedFixedDeepCode := by
  rcases chosen.pointer.cert.correct represented with ⟨reference,resolved,pathRun⟩ | ⟨refused,pathRun⟩
  · by_cases fits : cursor.val + max 1 count < W
    · obtain ⟨base',body,ran,allocated,root,extension,shape,below,gaps,kept,fresh⟩ :=
        checked_fixed_memory_success state.heap primitive count reference base frame cursor machine allocator fits
      let grown := (MVal.copyMToSt state.heap (T := .ref (.fixed (.prim primitive) count)) reference).copyStToM state.heap rfl
      have adopted : Objects.StateRepr L b frame frag (state.adopt grown).1 base' body :=
        represented.adopt grown allocated.heap extension shape (fun address lower upper =>
          below address (by omega) (Nat.lt_of_lt_of_le upper (Nat.le_trans represented.locals allocator.free.above)))
      refine .inl ⟨reference,resolved,fits,base',body,?_,adopted,allocated,root,extension,shape,below,gaps,kept,fresh⟩
      rw [SelectedAlias.checkedFixedDeepCode,run_append_ok pathRun]
      exact ran
    · right
      refine ⟨Or.inr ⟨reference,resolved,fits⟩,?_⟩
      rw [SelectedAlias.checkedFixedDeepCode,run_append_ok pathRun,
        checked_fixed_memory_run count machine cursor (base reference.id) allocator.free.cell,if_neg fits]
  · exact .inr ⟨Or.inl refused,run_append_revert pathRun⟩

theorem SelectedAlias.checkedFixedDeepBindExecute {C : Contract} {Γ : Ctx} {primitive : PrimTy} {count : Nat} {L b frame : Nat} {frag : Frag Γ}
    {path : MPath C Γ (.ref (.fixed (.prim primitive) count))} (chosen : SelectedAlias b frag path)
    {state : State C Γ} {base : Nat → Fin W} {cursor : Fin W} {machine : Machine}
    (represented : Objects.StateRepr L b frame frag state base machine)
    (allocator : Objects.AllocatorRepr state.heap base frame cursor machine) (positive : 0 < b)
    (destination : Idx Γ (.mem (.fixed (.prim primitive) count))) :
    CheckedFixedPathBindOutcome L b frame frag state base cursor machine path destination (chosen.checkedFixedDeepBindCode destination) := by
  rcases chosen.checkedFixedDeepExecute represented allocator positive with
    ⟨reference,resolved,fits,base',body,ran,adopted,allocated,root,extension,shape,below,_,kept,fresh⟩ | ⟨refused,failed⟩
  · let grown := (MVal.copyMToSt state.heap (T := .ref (.fixed (.prim primitive) count)) reference).copyStToM state.heap rfl
    let target := writeMachine body (cellOf b destination) (.val cursor)
    refine .inl ⟨reference,resolved,fits,base',target,?_,?_,?_,root,extension,?_,?_,?_,kept,fresh⟩
    · rw [SelectedAlias.checkedFixedDeepBindCode,run_append_ok ran]
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

def checkedFixedPathCopy : CheckedFixedPathCopyCertificate := ⟨SelectedAlias.checkedFixedDeepExecute,SelectedAlias.checkedFixedDeepBindExecute⟩

#print axioms SelectedAlias.checkedFixedDeepExecute
#print axioms SelectedAlias.checkedFixedDeepBindExecute
#print axioms checkedFixedPathCopy
end Solidity.Backend.MemoryCopies
