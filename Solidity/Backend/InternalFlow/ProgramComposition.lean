import Solidity.Evm.MemoryCalls
import Solidity.Semantics.DeferredSource

/-! Whole-program composition of actual published memory-call certificates.
The composed code is an owned emitter; no public compiler selector is changed.
Reached costs count the suffix only after a successful prefix. -/
namespace Solidity.Backend.InternalFlow.ProgramComposition
open Evm Evm.Memory
variable {C : Contract}

/-- Two checked programs, possibly with different private frame requirements,
compose through their actual typed intermediate context and fragment. -/
def join {b : Nat} {Γ Δ Ξ : Ctx} {F : Frag Γ}
    {P : Prog C Γ Δ} {Q : Prog C Δ Ξ}
    (first : Calls.Program b F P) (second : Calls.Program b first.frag Q) :
    Calls.Program b F (P.join Q) where
  frag := second.frag
  code := first.code ++ second.code
  need := max first.need second.need
  cost σ := first.cost σ + match P.run σ with
    | .ok out => second.cost out.st
    | .error _ => 0
  allocates := first.allocates || second.allocates
  zeroCost := by
    intro h σ
    have hs := Bool.or_eq_false_iff.mp h
    rw [first.zeroCost hs.1 σ]
    cases P.run σ with
    | error e => rfl
    | ok out => exact (Nat.zero_add _).trans (second.zeroCost hs.2 out.st)
  sound := by
    intro L frame σ base m repr room capacity
    have firstRoom : b + first.need ≤ frame := by omega
    have secondRoom : b + second.need ≤ frame := by omega
    have firstInput := capacity.of_le (Nat.le_add_right (first.cost σ) _)
    rcases first.sound repr firstRoom firstInput with
      ⟨out,m₁,base₁,source,target,repr₁,stack₁,extends₁,grows₁⟩ | ⟨source,target⟩
    · change P.runR σ = .ok out at source
      rw [DeferredSource.join_run,TRun.seq,source,Evm.run_append_ok target]
      have reached : AllocationInput b frame (first.cost σ + second.cost out.st) σ base m := by
        simpa only [source] using capacity
      rcases second.sound repr₁ secondRoom (grows₁.nextInput reached) with
        ⟨out₂,m₂,base₂,source₂,target₂,repr₂,stack₂,extends₂,grows₂⟩ | ⟨source₂,target₂⟩
      · refine .inl ⟨⟨out₂.st,out.ext.trans out₂.ext⟩,m₂,base₂,?_,target₂,repr₂,
          stack₂.trans stack₁,extends₁.trans out.ext extends₂,?_⟩
        · change Q.runR out.st = .ok out₂ at source₂
          dsimp only
          rw [source₂];rfl
        · simpa only [source] using grows₁.comp grows₂
      · change Q.runR out.st = .error .revert at source₂
        exact .inr ⟨by dsimp only; rw [source₂];rfl,target₂⟩
    · change P.runR σ = .error .revert at source
      refine .inr ⟨?_,Evm.run_append_revert target⟩
      rw [DeferredSource.join_run,TRun.seq,source]

/-- Metadata equations expose only constructor projections, not a fresh
normalization of either public compiler invocation. -/
theorem fields {b : Nat} {Γ Δ Ξ : Ctx} {F : Frag Γ}
    {P : Prog C Γ Δ} {Q : Prog C Δ Ξ}
    (first : Calls.Program b F P) (second : Calls.Program b first.frag Q) :
    (join first second).code = first.code ++ second.code ∧
    (join first second).frag = second.frag ∧
    (join first second).need = max first.need second.need := ⟨rfl,rfl,rfl⟩

theorem cost_success {b : Nat} {Γ Δ Ξ : Ctx} {F : Frag Γ}
    {P : Prog C Γ Δ} {Q : Prog C Δ Ξ}
    (first : Calls.Program b F P) (second : Calls.Program b first.frag Q)
    (σ : State C Γ) (out : Out C σ.H Δ) (executed : P.run σ = .ok out) :
    (join first second).cost σ = first.cost σ + second.cost out.st := by
  change first.cost σ + (match P.run σ with | .ok o => second.cost o.st | .error _ => 0) = _
  rw [executed]

theorem cost_failure {b : Nat} {Γ Δ Ξ : Ctx} {F : Frag Γ}
    {P : Prog C Γ Δ} {Q : Prog C Δ Ξ}
    (first : Calls.Program b F P) (second : Calls.Program b first.frag Q)
    (σ : State C Γ) (halt : THalt) (executed : P.run σ = .error halt) :
    (join first second).cost σ = first.cost σ := by
  change first.cost σ + (match P.run σ with | .ok o => second.cost o.st | .error _ => 0) = _
  rw [executed,Nat.add_zero]
end Solidity.Backend.InternalFlow.ProgramComposition
