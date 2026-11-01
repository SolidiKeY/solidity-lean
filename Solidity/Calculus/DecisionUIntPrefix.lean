import Solidity.Calculus.DecisionUIntFormula

/-!
# A positive primitive-prefix source bridge

Connect intrinsic arithmetic source shapes to the actual normalization and
source-reduction functions. This is not an exhaustive target/Residue result.
-/
namespace Solidity.Decide

/-- One positive primitive binder over an actual scoped equation. -/
def primitivePrefixEq {C : Contract} {p : PrimTy} (x : Var)
    (a b : Tm C [.val p] (.val p)) : Fml C [] := .all x p (.eq a b)

/-- This source shape consumes only its two formula nodes in the unchanged normalizer. -/
theorem primitivePrefixEq_normalizes {C : Contract} {p : PrimTy} (x : Var)
    (a b : Tm C [.val p] (.val p)) :
    (ProgramNormalization.ofFormula? 2048 (primitivePrefixEq x a b)).map (·.formula) =
      some (primitivePrefixEq x a b) := by
  rfl

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

/-- Actual equal-polarity translations pass the source reducer's checked comparison. -/
theorem directional_leaf_of_polarities {C : Contract} {Γ : Ctx}
    (ρ : SymS C Γ) (φ : Fml C Γ) (ψ : LFml C)
    (hp : φ.toLS true ρ = some ψ) (hn : φ.toLS false ρ = some ψ) :
    (ExactAt.directional? ρ φ).map (·.leaf) = some ψ := by
  unfold ExactAt.directional?
  split
  · rename_i hP
    rw [hP] at hp
    cases hp
  · rename_i P hP
    have eP : P = ψ := Option.some.inj (hP.symm.trans hp)
    subst P
    split
    · rename_i hN
      rw [hN] at hn
      cases hn
    · rename_i N hN
      have eN : N = ψ := Option.some.inj (hN.symm.trans hn)
      subst N
      split
      · rfl
      · rename_i he
        exact False.elim (he (leafFormula_same_self ψ))

/-- The original source reducer accepts this intrinsic uint-prefix family. -/
theorem uintPrefix_sourceReduction {C : Contract} (x : Var)
    {a b : Tm C [.val .uint] (.val .uint)} (ha : a.UIntLinear) (hb : b.UIntLinear) :
    ∃ ψ : LFml C,
      (sourceReduction? (primitivePrefixEq x a b)).map (·.leaf) = some (.all 0 .uint ψ) ∧
      ψ.Src false true := by
  have hρ : UIntSourceLocs ((SymS.init (C := C)).pushQ .uint) := UIntSourceLocs.pushQ UIntSourceLocs.init
  obtain ⟨ψ, hp, hn, hs⟩ := qfUIntLinear_toLS (Fml.QFUIntLinear.eq ha hb) ((SymS.init (C := C)).pushQ .uint) hρ
  have hd : (ExactAt.directional? ((SymS.init (C := C)).pushQ .uint) (.eq a b)).map (·.leaf) = some ψ :=
    directional_leaf_of_polarities ((SymS.init (C := C)).pushQ .uint) (.eq a b) ψ hp hn
  cases hr : ExactAt.directional? ((SymS.init (C := C)).pushQ .uint) (.eq a b) with
  | none => rw [hr] at hd; cases hd
  | some r =>
    rw [hr] at hd
    have hl : r.leaf = ψ := Option.some.inj hd
    refine ⟨ψ, ?_, hs⟩
    simp only [primitivePrefixEq, sourceReduction?, ExactAt.ofFormula?, Option.bind_eq_bind, Option.pure_def, hr,
      Option.orElse_some, Option.map_some, Option.bind_some, ExactAt.all]
    exact congrArg (fun B : LFml C => some (LFml.all 0 .uint B)) hl

/-- Successful actual normalization and source reduction compose through the unchanged leaf preparation. -/
theorem leafOf_of_normalized_source {C : Contract} (φ : Fml C []) (ψ : LFml C)
    (hn : (ProgramNormalization.ofFormula? 2048 φ).map (·.formula) = some φ)
    (hs : (sourceReduction? φ).map (·.leaf) = some ψ) :
    leafOf? φ = some ψ.elim.condSimp.prenex := by
  cases he : ProgramNormalization.ofFormula? 2048 φ with
  | none => rw [he] at hn; cases hn
  | some d =>
    rw [he] at hn
    have hf : d.formula = φ := Option.some.inj hn
    have ht : (sourceReduction? φ).map (fun r => r.leaf.elim.condSimp.prenex) =
        some ψ.elim.condSimp.prenex := by
      have h : ((sourceReduction? φ).map (·.leaf)).map
          (fun l : LFml C => l.elim.condSimp.prenex) = some ψ.elim.condSimp.prenex := congrArg (Option.map (fun l : LFml C => l.elim.condSimp.prenex)) hs
      simpa only [Option.map_map, Option.map_some] using h
    simp only [leafOf?, he, Option.bind_eq_bind, Option.pure_def, Option.bind_some]
    simp only [Option.map_eq_bind, Function.comp_def] at ht
    have ht' : ((sourceReduction? d.formula).bind fun r => some r.leaf.elim.condSimp.prenex) =
        some ψ.elim.condSimp.prenex := by
      exact hf.symm ▸ ht
    exact ht'

/-- The positive uint-prefix grammar reaches the actual prepared leaf, without a coverage premise. -/
theorem uintPrefix_leafOf {C : Contract} (x : Var)
    {a b : Tm C [.val .uint] (.val .uint)} (ha : a.UIntLinear) (hb : b.UIntLinear) :
    ∃ ψ : LFml C, leafOf? (primitivePrefixEq x a b) =
      some (LFml.all 0 .uint ψ).elim.condSimp.prenex ∧ ψ.Src false true := by
  obtain ⟨ψ, hs, hsrc⟩ := uintPrefix_sourceReduction x ha hb
  exact ⟨ψ, leafOf_of_normalized_source _ _ (primitivePrefixEq_normalizes x a b) hs, hsrc⟩

end Solidity.Decide
