import Solidity.Calculus.DecideTyped

/-!
# Exact reductions of scoped formulas

The ordinary reducer is intentionally directional: a positive reduction
proves a formula, while a negative-polarity reduction follows from it. An
exact reduction accepts only when both computations produce the same leaf.
Its certificate contains computation equalities, not a semantic assumption.
Pending programs, updates and hidden binders rejected by negative reduction
remain outside this initial exact fragment.
-/

namespace Solidity.Decide

variable {C : Contract}

/-- Structural comparison of the existing typed leaf language. -/
def LFml.same : LFml C → LFml C → Bool
  | .tt, .tt => true
  | @LFml.eq _ p a b, @LFml.eq _ q x y =>
    if h : q = p then a.beqR (h ▸ x) && b.beqR (h ▸ y) else false
  | .not φ, .not ψ => φ.same ψ
  | .and φ χ, .and ψ θ | .imp φ χ, .imp ψ θ => φ.same ψ && χ.same θ
  | .all k p φ, .all j q ψ => k == j && p == q && φ.same ψ
  | _, _ => false

/-- A successful comparison is equality of the complete leaf formulas. -/
theorem LFml.eq_of_same (φ ψ : LFml C) (h : φ.same ψ = true) : φ = ψ := by
  induction φ generalizing ψ with
  | tt => cases ψ <;> simp_all only [LFml.same, Bool.false_eq_true]
  | eq a b =>
    cases ψ with
    | eq x y =>
      simp only [LFml.same] at h
      split at h
      · next he =>
        subst he
        simp only [Bool.and_eq_true] at h
        obtain ⟨ha, hb⟩ := h
        cases LTm.eq_of_beqR ha
        cases LTm.eq_of_beqR hb
        rfl
      · cases h
    | _ => cases h
  | not φ ih =>
    cases ψ with
    | not ψ => exact congrArg LFml.not (ih ψ h)
    | _ => cases h
  | and φ χ ihφ ihχ =>
    cases ψ with
    | and ψ θ =>
      simp only [LFml.same, Bool.and_eq_true] at h
      obtain ⟨hφ, hχ⟩ := h
      cases ihφ ψ hφ
      cases ihχ θ hχ
      rfl
    | _ => cases h
  | imp φ χ ihφ ihχ =>
    cases ψ with
    | imp ψ θ =>
      simp only [LFml.same, Bool.and_eq_true] at h
      obtain ⟨hφ, hχ⟩ := h
      cases ihφ ψ hφ
      cases ihχ θ hχ
      rfl
    | _ => cases h
  | all k p φ ih =>
    cases ψ with
    | all j q ψ =>
      simp only [LFml.same, Bool.and_eq_true] at h
      obtain ⟨⟨hk, hp⟩, hφ⟩ := h
      have hk' : k = j := eq_of_beq hk
      have hp' : p = q := eq_of_beq hp
      cases hk'
      cases hp'
      cases ih ψ hφ
      rfl
    | _ => cases h

/-- An exact reduction is witnessed by both directional computations. -/
structure ExactReduction (φ : Fml C []) where
  leaf : LFml C
  positive : φ.toLS true SymS.init = some leaf
  negative : φ.toLS false SymS.init = some leaf

/-- Both certified directions give equality of meaning in every initial
typed state, before read elimination. -/
theorem ExactReduction.holds_iff {φ : Fml C []} (r : ExactReduction φ) (σ : State C []) :
    r.leaf.holds σ AEnv.dflt ↔ holds σ φ := by
  exact ⟨(Fml.toLS_sound φ true r.positive σ AEnv.dflt
      (Agrees.init σ AEnv.dflt) SymS.Fresh.init).1 rfl,
    (Fml.toLS_sound φ false r.negative σ AEnv.dflt
      (Agrees.init σ AEnv.dflt) SymS.Fresh.init).2 rfl⟩

/-- Read-of-write elimination is exact as well; its negative result can
therefore be transported back through an exact reduction. -/
theorem ExactReduction.elim_holds_iff {φ : Fml C []} (r : ExactReduction φ) (σ : State C []) :
    r.leaf.elim.holds σ AEnv.dflt ↔ holds σ φ :=
  (LFml.elim_holds σ r.leaf AEnv.dflt).trans (r.holds_iff σ)

/-- A countermodel of an exact reduced leaf refutes the original formula. -/
theorem ExactReduction.refutes {φ : Fml C []} (r : ExactReduction φ) (σ : State C [])
    (h : ¬ r.leaf.elim.holds σ AEnv.dflt) : ¬ Fml.Valid φ :=
  fun hv => h ((r.elim_holds_iff σ).2 (hv σ))

/-- Produce an exact certificate only after both reductions and their
structural agreement have succeeded. `none` makes no validity claim. -/
def exactReduction? (φ : Fml C []) : Option (ExactReduction φ) := do
  match hp : φ.toLS true SymS.init with
  | none => none
  | some p =>
    match hn : φ.toLS false SymS.init with
    | none => none
    | some n =>
      if he : p.same n = true then
        some ⟨p, hp, (LFml.eq_of_same p n he) ▸ hn⟩
      else none

end Solidity.Decide
