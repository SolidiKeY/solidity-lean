import Solidity.Calculus.Sound.ExternalTryWitness
import Solidity.Semantics.TryConditions

/-! Exact guarded ordinary formulas. No guard becomes a global admissibility
premise or a callback proof. Continuations/frames and every halt are retained. -/
namespace Solidity

/-- The existing diamond accepts normal postconditions *or exhaustion*. This
is not an equivalence with normal termination alone. -/
theorem diamond_result_iff {α : Type} (p : α → Prop) (r : TRes α) :
    Modality.afterRunTR .diamond p r ↔
      (∃ a, r = .ok a ∧ p a) ∨ r = .error .exhausted := by
  cases r with
  | ok a =>
    constructor
    · intro h; exact .inl ⟨a, rfl, h.1⟩
    · intro h
      rcases h with ⟨b, hb, hp⟩ | he
      · cases hb; exact ⟨hp, by intro h; cases h⟩
      · cases he
  | error e =>
    constructor
    · intro h
      have he : e = .exhausted := h.1
      cases he; exact .inr rfl
    · intro h
      rcases h with ⟨a, ha, _⟩ | he
      · cases ha
      · cases he
        exact ⟨rfl, by intro h; cases h⟩

/-- Full ordinary formula account, including failures in continuations or
scope frames after a normally completed try/catch. -/
theorem holds_diamond_outcomes_iff {C : Contract} {Γ Δ Ω : Ctx}
    (σ : State C Γ) (P : Prog C Γ Δ) (frames : Frames C Δ Ω) (φ : Fml C Ω) :
    holds σ (.modal .diamond P frames φ) ↔
      (∃ τ, Prog.runFrames σ P frames = .ok τ ∧ holds τ φ) ∨
        Prog.runFrames σ P frames = .error .exhausted :=
  diamond_result_iff (holds · φ) _

/-- Explicit actual-outcome guards give the precise ordinary formula, with
arbitrary remaining program and frames. No source or callback validity follows. -/
theorem try_condition_formula {C : Contract} {Γ ρ κ Γ₁ Γ₂ Γ₃ Γ₄ ps Γf Δ Ω : Ctx}
    (call : ExtCall C Γ) (rets : Binders ρ) (ok : Prog C (ρ ++ Γ) Γ₁)
    (err : Prog C Γ Γ₂) (code : CodeBinder κ) (pnc : Prog C (κ ++ Γ) Γ₃)
    (other : Prog C Γ Γ₄) (sargs : Args C Γ ps) (sbody : Prog C (ρ ++ ps) Γf)
    (self : Bool) (σ : State C Γ) (r : TRes (Out C σ.H Γ))
    (h : TRun.tryCondition call rets ok err code pnc other sargs sbody self σ r)
    (rest : Prog C Γ Δ) (frames : Frames C Δ Ω) (φ : Fml C Ω) :
    holds σ (.modal .diamond
      (.cons (.tryCall call rets ok err code pnc other sargs sbody self) rest) frames φ) ↔
    Modality.afterRunTR .diamond (holds · φ)
      ((r.map (·.st)).bind fun τ => (Prog.runSt τ rest).bind (Frames.runSt · frames)) := by
  have hr : (Stmt.tryCall call rets ok err code pnc other sargs sbody self).run σ = r :=
    (TRun.tryCall_eq_iff call rets ok err code pnc other sargs sbody self σ r).2 h
  rw [holds_modal_iff, runSt_cons_frames]
  simp only [Stmt.runSt, hr]

/-- Payload clauses use the same guarded transport for normal results or any
handler/allocation halt; continuation and frame outcomes remain unchanged. -/
theorem catch_condition_formula {C : Contract} {Γ ρ ps Γf Γ₁ Δ Ω : Ctx}
    (call : ExtCall C Γ) (rets : Binders ρ) (sargs : Args C Γ ps)
    (sbody : Prog C (ρ ++ ps) Γf) (self : Bool) (σ : State C Γ)
    (kind : CatchKind) (x : Var) (body : Prog C (.mem bytesR :: Γ) Γ₁)
    (r : TRes (Out C σ.H Γ))
    (h : TRun.catchCondition call rets sargs sbody self σ kind body r)
    (rest : Prog C Γ Δ) (frames : Frames C Δ Ω) (φ : Fml C Ω) :
    holds σ (.modal .diamond
      (.cons (.catchData call rets sargs sbody self kind x body) rest) frames φ) ↔
    Modality.afterRunTR .diamond (holds · φ)
      ((r.map (·.st)).bind fun τ => (Prog.runSt τ rest).bind (Frames.runSt · frames)) := by
  have hr : (Stmt.catchData call rets sargs sbody self kind x body).run σ = r :=
    (TRun.catchData_eq_iff call rets sargs sbody self σ kind body r).2 h
  rw [holds_modal_iff, runSt_cons_frames]
  simp only [Stmt.runSt, hr]

/-- info: 'Solidity.try_condition_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms try_condition_formula

end Solidity
