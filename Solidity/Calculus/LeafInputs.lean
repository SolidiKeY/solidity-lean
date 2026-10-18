import Solidity.Calculus.LeafArithmetic

/-!
# The actual typed inputs of a leaf

Agreement is required only at the typed atom positions a term reads.
This connects universal-prefix instantiation to fresh read flattening:
the original body uses declared parameters; the extra result atoms are
introduced only after those source inputs have been identified.
-/

namespace Solidity.Decide

variable {C : Contract}

def Parameters.Agree (ps : List Parameter) (ν μ : AEnv) : Prop :=
  ∀ p ∈ ps, p.read ν = p.read μ

theorem Parameters.Agree.left {ps qs : List Parameter} {ν μ : AEnv}
    (h : Agree (ps ++ qs) ν μ) : Agree ps ν μ :=
  fun p hp => h p (List.mem_append_left _ hp)

theorem Parameters.Agree.right {ps qs : List Parameter} {ν μ : AEnv}
    (h : Agree (ps ++ qs) ν μ) : Agree qs ν μ :=
  fun p hp => h p (List.mem_append_right _ hp)

theorem LTm.eval_agree_parameters (g : State C []) {s : Srt} (t : LTm C s) {ν μ : AEnv}
    (h : Parameters.Agree t.parameters ν μ) : t.eval g ν = t.eval g μ := by
  induction t with
  | var k => exact congrArg some (h _ List.mem_cons_self)
  | app0 o | err => rfl
  | app1 o a ih => rw [eval_app1, eval_app1, ih h]
  | app2 o a b iha ihb => rw [eval_app2, eval_app2, iha h.left, ihb h.right]
  | app3 o a b c iha ihb ihc => rw [eval_app3, eval_app3, iha h.left.left, ihb h.left.right, ihc h.right]
  | index it a b iha ihb => rw [eval_index, eval_index, iha h.left, ihb h.right]
  | obsW a ih => rw [eval_obsW, eval_obsW, ih h]
  | obsL a ih => rw [eval_obsL, eval_obsL, ih h]
  | obsH a ih => rw [eval_obsH, eval_obsH, ih h]
  | seq a b iha ihb => rw [eval_seq, eval_seq, iha h.left, ihb h.right]
  | orElse a b iha ihb => rw [eval_orElse, eval_orElse, iha h.left, ihb h.right]
  | kite a b t e iha ihb iht ihe =>
    rw [eval_kite, eval_kite, iha h.left.left.left, ihb h.left.left.right, iht h.left.right, ihe h.right]

theorem ReadFormula.holds_agree_parameters {φ : LFml C} (r : ReadFormula φ) (g : State C [])
    {ν μ : AEnv} (h : Parameters.Agree φ.parameters ν μ) : φ.holds g ν ↔ φ.holds g μ := by
  induction r with
  | tt => rfl
  | @eq p t w a b => simp only [LFml.holds, t.eval_agree_parameters g h.left, w.eval_agree_parameters g h.right]
  | not r ih => exact not_congr (ih h)
  | and r s ihr ihs => exact and_congr (ihr h.left) (ihs h.right)
  | imp r s ihr ihs => exact imp_congr (ihr h.left) (ihs h.right)

theorem ReadFormula.holds_assign {φ : LFml C} (r : ReadFormula φ) (g : State C [])
    (ps : List Parameter) (hc : ∀ p ∈ φ.parameters, p ∈ ps) (base chosen : AEnv) :
    φ.holds g (Parameters.assign ps chosen base) ↔ φ.holds g chosen := by
  apply r.holds_agree_parameters g
  intro p hp
  simpa only [hc p hp, ↓reduceIte] using Parameters.read_assign ps p chosen base

end Solidity.Decide
