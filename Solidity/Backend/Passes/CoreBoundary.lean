import Solidity.Backend.Passes.MappedSequence

/-! Physical projection into an existing core suffix, for all eleven actual
Compilation branches. This does not upgrade core Sim into heap ownership. -/
namespace Solidity.Backend.Passes
open Solidity.Evm Solidity.Evm.Compiler
variable {C : Contract} {b L frame : Nat} {Γ Δ Ξ : Ctx}
  {F : Frag Γ} {P : Prog C Γ Δ} {Q : Prog C Δ Ξ}

theorem mapped_output_core (result : Compilation b F P)
    {base outBase : Nat → Fin W} {σ : State C Γ} {initial m : Machine} {τ : State C Δ}
    (h : MappedOutput result L frame base σ initial τ m outBase) :
    Sim C L b result.frag τ m := by
  cases result with
  | core out cert => exact h.2
  | memory out => exact h.1.core
  | referenceArrays out => exact h.2.state.core
  | objects out => exact h.2.1.core
  | construction out => exact h.1.core
  | memoryLoops out =>
    rcases h with ⟨_,_,_,state,_,_⟩
    exact state.core
  | memoryLoopScopes out =>
    rcases h with ⟨_,_,_,state,_,_⟩
    exact state.core
  | memoryCalls out pushFree => exact h.1.core
  | memoryCopy out => exact h.1.core
  | fixedMemory out => exact h.2.1.legacy.core
  | copyConstruction out => exact h.1.core

theorem compilation_rep_core (result : Compilation b F P)
    {base : Nat → Fin W} {σ : State C Γ} {initial m : Machine} {τ : State C Δ}
    (h : result.Rep L frame base σ initial τ m) : Sim C L b result.frag τ m := by
  obtain ⟨outBase, hm⟩ := (mapped_output_iff result _ _ _ _ _ _ _).mp h
  exact mapped_output_core result hm

/-- No desired suffix preservation or heap assertion is a premise: only the
original independently checked core certificate and its reached push bound. -/
theorem compilation_core_mapped_link (left : Compilation b F P)
    {G : Frag Ξ} (cert : inFragP left.frag Q = some G)
    {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (bound : (L + Evm.Prog.pushes P) + Evm.Prog.pushes Q ≤ Lmax) :
    MappedBoundaryLink left (.core G cert) L frame base σ m := by
  intro o mid selected _ _ h
  exact ⟨mapped_output_core left h, bound⟩

theorem compilation_core_link (left : Compilation b F P)
    {G : Frag Ξ} (cert : inFragP left.frag Q = some G)
    {base nextBase : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (bound : (L + Evm.Prog.pushes P) + Evm.Prog.pushes Q ≤ Lmax) :
    BoundaryLink left (.core G cert) L frame base nextBase σ m := by
  intro o mid _ _ h
  exact ⟨compilation_rep_core left h, bound⟩

/-- Retaining the core certificate alone cannot remove its resource Input. -/
theorem core_input_refused {G : Frag Δ} (cert : inFragP F P = some G)
    {σ : State C Γ} {m : Machine} {base : Nat → Fin W}
    (bound : Lmax < L + Evm.Prog.pushes P) :
    ¬ (Compilation.core (b := b) G cert).Input L frame base σ m := by
  intro h
  exact (Nat.not_le_of_lt bound) h.2

end Solidity.Backend.Passes
