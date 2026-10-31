import Solidity.Calculus.TermWk
import Solidity.Calculus.Logic

/-!
# Quantified loop invariants under typed ghost locals

A variant snapshot adds a local outside the invariant's quantifiers.
Weakening keeps every bound variable at its own type and position; it
preserves the Theory reading, including undefined operands in implications.
-/
namespace Solidity
variable {C : Contract}

/-- A clause such as `\forall uint q; q < i -> q < n` reads alike
under any typed context embedding, including beneath its own binders. -/
theorem LoopQ.toFml_wk_holds {Γ Δ : Ctx} (h : Thin Γ Δ)
    (q : LoopQ C Γ) (σ : State C Δ) :
    holds σ (q.wk h).toFml ↔ holds (σ.thin h) q.toFml := by
  induction q generalizing Δ with
  | val a =>
    simp only [LoopQ.wk, LoopQ.toFml, Fml.isBool, holds, Val.lower_wk,
      Tm.denote_wk, Tm.denote, Op0.denote]
  | imp a b =>
    simp only [LoopQ.wk, LoopQ.toFml, Fml.isBool, holds, Val.lower_wk,
      Tm.denote_wk, Tm.denote, Op0.denote]
  | all x p b ih =>
    change (∀ v : p.Denote, holds (σ.push v) (b.wk h.keep).toFml) ↔
      (∀ v : p.Denote, holds ((σ.thin h).push v) b.toFml)
    apply forall_congr'
    intro v
    exact ih h.keep (σ.push v)

/-- Weakening the complete invariant of `while (i < n)` preserves its
reading: no quantified conjunct is lost under the variant snapshot. -/
theorem invFml_wk_holds {Γ Δ : Ctx} (h : Thin Γ Δ)
    (I : Val C Γ .bool) (qs : List (LoopQ C Γ)) (σ : State C Δ) :
    holds σ (invFml (I.wk h) (qs.map (LoopQ.wk h))) ↔
      holds (σ.thin h) (invFml I qs) := by
  suffices aux : ∀ (qs : List (LoopQ C Γ)) (a : Fml C Γ) (b : Fml C Δ),
      (holds σ b ↔ holds (σ.thin h) a) →
      (holds σ (List.foldl (fun acc q => Fml.and acc q.toFml) b (qs.map (LoopQ.wk h))) ↔
       holds (σ.thin h) (List.foldl (fun acc q => Fml.and acc q.toFml) a qs)) by
    apply aux qs
    simp only [holds, Val.lower_wk, Tm.denote_wk, Tm.denote, Op0.denote]
  intro qs
  induction qs with
  | nil => intros; assumption
  | cons q qs ih =>
    intro a b hab
    exact ih (.and a q.toFml) (.and b (q.wk h).toFml)
      (and_congr hab (q.toFml_wk_holds h σ))

/-- A scalar variant's ghost local cannot change a quantified invariant. -/
theorem invFml_up_holds {Γ : Ctx} {t : LTy} (I : Val C Γ .bool)
    (qs : List (LoopQ C Γ)) (σ : State C Γ) (v : t.TDenote C σ.H) :
    holds (σ.push v) (invFml I.up (qs.map LoopQ.up)) ↔ holds σ (invFml I qs) := by
  rw [Val.up_eq]
  exact invFml_wk_holds (.drop .refl) I qs (σ.push v)
end Solidity
