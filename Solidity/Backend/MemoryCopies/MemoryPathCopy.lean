import Solidity.Backend.MemoryCopies.MemoryPathCopyInterface

/-! Existing pointer correctness resolves the actual copied object or refuses
before allocation. Existing ownership transport adopts and binds the copy. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

theorem SelectedAlias.deepExecute {C : Contract} {Γ : Ctx} {primitive : PrimTy} {L b frame : Nat} {frag : Frag Γ}
    {path : MPath C Γ (.ref (.array (.prim primitive)))} (chosen : SelectedAlias b frag path)
    {state : State C Γ} {base : Nat → Fin W} {cursor : Fin W} {machine : Machine}
    (represented : Objects.StateRepr L b frame frag state base machine)
    (allocator : Objects.AllocatorRepr state.heap base frame cursor machine) (positive : 0 < b)
    (fits : MemoryPathRoom state cursor path) :
    MemoryPathCopyOutcome L b frame frag state base cursor machine path chosen.deepCode fits := by
  rcases chosen.pointer.cert.correct represented with ⟨reference,resolved,pathRun⟩ | ⟨refused,pathRun⟩
  · obtain ⟨base',body,ran,allocated,root,extension,shape,below,gaps,kept,fresh⟩ :=
      runtime_memory_array_success state.heap primitive reference base frame cursor machine allocator (fits reference resolved)
    let grown := (MVal.copyMToSt state.heap (T := .ref (.array (.prim primitive))) reference).copyStToM state.heap rfl
    have adopted : Objects.StateRepr L b frame frag (state.adopt grown).1 base' body :=
      represented.adopt grown allocated.heap extension shape (fun address lower upper =>
        below address (by omega) (Nat.lt_of_lt_of_le upper (Nat.le_trans represented.locals allocator.free.above)))
    refine .inl ⟨reference,resolved,base',body,?_,adopted,allocated,root,extension,shape,below,gaps,kept,fresh⟩
    rw [SelectedAlias.deepCode,run_append_ok pathRun]
    exact ran
  · exact .inr ⟨refused,run_append_revert pathRun⟩

theorem SelectedAlias.deepBindExecute {C : Contract} {Γ : Ctx} {primitive : PrimTy} {L b frame : Nat} {frag : Frag Γ}
    {path : MPath C Γ (.ref (.array (.prim primitive)))} (chosen : SelectedAlias b frag path)
    {state : State C Γ} {base : Nat → Fin W} {cursor : Fin W} {machine : Machine}
    (represented : Objects.StateRepr L b frame frag state base machine)
    (allocator : Objects.AllocatorRepr state.heap base frame cursor machine) (positive : 0 < b)
    (fits : MemoryPathRoom state cursor path) (destination : Idx Γ (.mem (.array (.prim primitive)))) :
    MemoryPathBindOutcome L b frame frag state base cursor machine path destination (chosen.deepBindCode destination) fits := by
  rcases chosen.deepExecute represented allocator positive fits with
    ⟨reference,resolved,base',body,ran,adopted,allocated,root,extension,shape,below,_,kept,fresh⟩ | ⟨refused,failed⟩
  · let grown := (MVal.copyMToSt state.heap (T := .ref (.array (.prim primitive))) reference).copyStToM state.heap rfl
    let target := writeMachine body (cellOf b destination) (.val cursor)
    refine .inl ⟨reference,resolved,base',target,?_,?_,?_,root,extension,?_,?_,?_,kept,fresh⟩
    · rw [SelectedAlias.deepBindCode,run_append_ok ran]
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

def memoryPathCopy : MemoryPathCopyCertificate := ⟨SelectedAlias.deepExecute,SelectedAlias.deepBindExecute⟩

#print axioms SelectedAlias.deepExecute
#print axioms SelectedAlias.deepBindExecute
#print axioms memoryPathCopy
end Solidity.Backend.MemoryCopies
