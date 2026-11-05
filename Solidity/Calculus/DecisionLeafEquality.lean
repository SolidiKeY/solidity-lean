import Solidity.Calculus.ExactReduction

/-! # Existing leaf self-comparison facts below the Decision facade
Public theorem names, proofs and recursion layout are preserved verbatim.
-/
namespace Solidity.Decide

/-- Structural self-comparison of the existing typed leaf terms. -/
theorem leafTerm_beq_self {C : Contract} {s : Srt} (t : LTm C s) : t.beqR t = true := by
  rw [LTm.beqR_eq_beqM]
  induction t with
  | var k => simp only [LTm.beqM, beq_self_eq_true, Bool.and_self]
  | app0 o => simp only [LTm.beqM, Op0.hbeq, hbeqAt_self]
  | app1 o x ih => simp only [LTm.beqM, Op1.hbeq_self, ih, Bool.and_self]
  | app2 o x y ihx ihy => simp only [LTm.beqM, Op2.hbeq_self, ihx, ihy, Bool.and_self]
  | app3 o x y z ihx ihy ihz =>
    simp only [LTm.beqM, Op3.hbeq_self, ihx, ihy, ihz, Bool.and_self]
  | index it q i ihq ihi =>
    simp only [LTm.beqM, ihq, ihi, Bool.and_true, decide_eq_true_eq, true_and]
  | obsW q ih | obsL q ih | obsH q ih => exact ih
  | seq d a ihd iha | orElse d a ihd iha => simp only [LTm.beqM, ihd, iha, Bool.and_self]
  | kite a b t e iha ihb iht ihe =>
    simp only [LTm.beqM, iha, ihb, iht, ihe, Bool.and_self]
  | err => simp only [LTm.beqM, beq_self_eq_true]

/-- The existing formula comparison accepts every identical typed formula. -/
theorem leafFormula_same_self {C : Contract} (φ : LFml C) : φ.same φ = true := by
  induction φ with
  | tt => rfl
  | eq a b =>
    simp only [LFml.same, leafTerm_beq_self, Bool.and_self]
    rfl
  | not φ ih => exact ih
  | and φ ψ ihφ ihψ | imp φ ψ ihφ ihψ =>
    simp only [LFml.same, ihφ, ihψ, Bool.and_self]
  | all k p φ ih =>
    simp only [LFml.same, beq_self_eq_true, ih, Bool.and_self]

end Solidity.Decide
