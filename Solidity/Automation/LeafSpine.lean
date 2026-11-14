import Solidity.Calculus.DecideLang

/-! A structural terminal-leaf checker. It never evaluates an implication's
premise or a state-dependent term. Failure means only that this fragment did
not close the leaf; callers must retain their original verified closer. -/
namespace Solidity.Automation.Leaf
open Decide
variable {C : Contract}

/-- Truth, literal-true equations, conjunctions, implications with a valid
conclusion, and universal closures of these forms. -/
def spine : LFml C → Bool
  | .tt => true
  | @LFml.eq _ .bool a b => a.isTT && b.isTT
  | .and a b => spine a && spine b
  | .imp _ b => spine b
  | .all _ _ b => spine b
  | _ => false

theorem spine_valid {φ : LFml C} (h : spine φ = true) : φ.Valid := by
  induction φ with
  | tt => exact fun _ _ => True.intro
  | eq a b =>
    rename_i p
    cases p <;> try { simp only [spine, Bool.false_eq_true] at h }
    simp only [spine, Bool.and_eq_true] at h
    obtain ⟨ha, hb⟩ := h
    intro g ν
    simp only [LFml.holds, LTm.isTT_eval ha, LTm.isTT_eval hb]
  | not φ ih => simp only [spine, Bool.false_eq_true] at h
  | and a b iha ihb =>
    simp only [spine, Bool.and_eq_true] at h
    obtain ⟨ha, hb⟩ := h
    exact fun g ν => ⟨iha ha g ν, ihb hb g ν⟩
  | imp a b _ ihb => exact fun g ν _ => ihb h g ν
  | all k p b ih => exact fun g ν v => ih h g (ν.set p k v)

/-- Regression: a failed term must not become a reflexive equality proof. -/
example : spine (C := C) (.eq (p := .bool) .err .err) = false := rfl

/-- Irrelevant premises need not be evaluated. -/
example (P : LFml C) : spine (.all 0 .uint (.imp P (.and .tt .tt))) = true := rfl

end Solidity.Automation.Leaf
