import Solidity.Assurance.NonVacuityH28.Calculus

/-! Kernel controls for deliberately contradictory proof/fragment instances.
These are negative controls, never positive execution witnesses. -/
namespace Solidity.Assurance.NonVacuityH28
open Solidity Semantics

variable {C : Contract}

theorem done_false_antecedent_rejected {Γ Γ' Γ₁ Γ₀ : Ctx} (σ : State C Γ)
    (m : Modality) (ω : Prog C Γ' Γ₁) (κ : Frames C Γ₁ Γ₀) (φ : Fml C Γ₀) :
    ¬ holds σ ((Premise.done (C := C) (Γ := Γ) (Γ' := Γ') false).fml m ω κ φ) := by
  intro h
  exact h True.intro

theorem empty_goal_guard_rejected {α : Type} : ¬ ([] : List α).isEmpty = false := by
  intro h
  cases h

theorem empty_cases_guard_rejected {Γ : Ctx} :
    ¬ (([] : List (Fml C Γ)).isEmpty && ([] : List (Upd C Γ Γ)).isEmpty) = false := by
  intro h
  cases h

theorem callback_false_derivation_rejected (C : Contract) (pay : Bool) :
    ¬ ProvesC (Invariant.top (C := C)).fml pay [] .nil .ff := by
  intro h
  cases pay with
  | false =>
    have hv : Spec.ValidC (Invariant.top (C := C)) (.not .tt) false := Main.noCallback_soundness h
    exact hv (State.init C) True.intro
  | true =>
    have hv : Spec.ValidC (Invariant.top (C := C)) (.not .tt) true := Main.callback_soundness h
    exact hv (State.init C) True.intro

theorem violated_after_rejected {H : HTy} {Γ : Ctx} (m : Modality)
    (p : State C Γ → Prop) : ¬ (COut.violated (C := C) (H := H) (Γ := Γ)).after m p := by
  intro h
  exact h

def assumptionProgram (C : Contract) : Prog C [] [] := .cons .assumeFalse .nil

theorem assumption_exhausts (σ : State C []) :
    Prog.run σ (assumptionProgram C) = .error .exhausted := rfl

theorem assumption_not_successful (σ : State C []) :
    ¬ ∃ o, Prog.run σ (assumptionProgram C) = .ok o := by
  rintro ⟨o, ho⟩
  rw [assumption_exhausts] at ho
  cases ho

theorem assumption_fragment_rejected :
    Evm.inFragP (Evm.Frag.init []) (assumptionProgram C) = none := rfl

theorem assumption_erased_code (b : Nat) (mc : Evm.Machine) :
    Evm.run (Evm.compileProg b (assumptionProgram C)) mc = .ok mc 0 := rfl

theorem expression_nonrevert_halt_rejected {Γ : Ctx} {p : PrimTy}
    (σ : State C Γ) (v : Val C Γ p) (e : THalt) (hne : e ≠ .revert) :
    ¬ v.evalT σ = .error e := by
  intro h
  exact hne ((Val.evalT_revertOnly (σ := σ) v).error h)

end Solidity.Assurance.NonVacuityH28
