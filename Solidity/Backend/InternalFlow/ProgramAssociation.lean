import Solidity.Backend.InternalFlow.ProgramComposition
/-! Association of genuine typed program certificates. Reassociation changes
neither emitted code nor reached source allocation cost or maximum frame need. -/
namespace Solidity.Backend.InternalFlow.ProgramComposition
open Evm Evm.Memory
variable {C : Contract}

/-- Structural equality over the EXISTING intrinsic syntax, independent of
execution and without a call-height admission premise. -/
theorem syntax_association : {Γ Δ Ξ Ω : Ctx} → (P : Prog C Γ Δ) →
    (Q : Prog C Δ Ξ) → (R : Prog C Ξ Ω) → (P.join Q).join R = P.join (Q.join R)
  | _,_,_,_,.nil,Q,R => rfl
  | _,_,_,_,.cons s P,Q,R => congrArg (Prog.cons s) (syntax_association P Q R)

theorem association {b : Nat} {Γ Δ Ξ Ω : Ctx} {F : Frag Γ}
    {P : Prog C Γ Δ} {Q : Prog C Δ Ξ} {R : Prog C Ξ Ω}
    (first : Calls.Program b F P) (second : Calls.Program b first.frag Q)
    (third : Calls.Program b second.frag R) (σ : State C Γ) :
    (join (join first second) third).code = (join first (join second third)).code ∧
    (join (join first second) third).frag = (join first (join second third)).frag ∧
    (join (join first second) third).need = (join first (join second third)).need ∧
    (join (join first second) third).cost σ = (join first (join second third)).cost σ := by
  refine ⟨List.append_assoc _ _ _,rfl,Nat.max_assoc _ _ _,?_⟩
  dsimp only [join]
  rw [DeferredSource.join_run]
  cases hp : P.run σ with
  | error e =>
    have h : P.runR σ = .error e := hp
    simp only [h,TRun.seq,Nat.add_zero]
  | ok out =>
    have h : P.runR σ = .ok out := hp
    simp only [h,TRun.seq]
    cases hq : Q.run out.st with
    | error e =>
      have k : Q.runR out.st = .error e := hq
      simp only [k,Except.map,Nat.add_zero]
    | ok value =>
      have k : Q.runR out.st = .ok value := hq
      simp only [k,Except.map]
      exact Nat.add_assoc _ _ _
end Solidity.Backend.InternalFlow.ProgramComposition
