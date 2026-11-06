import Solidity.Backend.MemoryCopies.AliasBindingInterface

/-! Actual selected pointer execution followed by the existing local store. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

def selectedAlias {C : Contract} {Γ : Ctx} (b : Nat) (frag : Frag Γ)
    {R : RefTy} (path : MPath C Γ (.ref R))
    (available : (Objects.compilePtr b frag path).isSome = true) : SelectedAlias b frag path where
  pointer := (Objects.compilePtr b frag path).get available
  selected := (Option.some_get available).symm

def SelectedAlias.code {C : Contract} {Γ : Ctx} {b : Nat} {frag : Frag Γ}
    {R : RefTy} {path : MPath C Γ (.ref R)} (chosen : SelectedAlias b frag path)
    (destination : Idx Γ (.mem R)) : List Instr :=
  chosen.pointer.code ++ [.mstore (cellOf b destination)]

/-- No resolved path, source success or target run is assumed. The existing
pointer certificate determines either the actual reference or bounds refusal. -/
theorem SelectedAlias.execute {C : Contract} {Γ : Ctx} {L b frame : Nat} {frag : Frag Γ}
    {R : RefTy} {path : MPath C Γ (.ref R)} (chosen : SelectedAlias b frag path)
    {state : State C Γ} {base : Nat → Fin W} {machine : Machine}
    (represented : Objects.StateRepr L b frame frag state base machine)
    (destination : Idx Γ (.mem R)) :
    AliasBindingOutcome L b frame frag state base machine path destination (chosen.code destination) := by
  rcases chosen.pointer.cert.correct represented with ⟨reference, resolved, execution⟩ | ⟨refused, execution⟩
  · refine .inl ⟨reference, writeMachine machine (cellOf b destination) (.val (base reference.id)),
      resolved, ?_, ?_, represented.setMem destination reference, rfl, ?_⟩
    · simp only [TRun.rebindMem, MRhs.evalT, resolved, bind, Except.bind, pure, Except.pure]
    · rw [SelectedAlias.code, run_append_ok execution]
      rfl
    · intro cursor positive allocator
      exact allocator.localWrite _ (Nat.lt_of_lt_of_le positive (le_lvl b destination))
        (Nat.lt_of_lt_of_le (lvl_lt b destination) represented.locals) _
  · refine .inr ⟨refused, ?_, ?_⟩
    · simp only [TRun.rebindMem, MRhs.evalT, refused, bind, Except.bind]
    · exact run_append_revert execution

#print axioms selectedAlias
#print axioms SelectedAlias.execute
end Solidity.Backend.MemoryCopies
