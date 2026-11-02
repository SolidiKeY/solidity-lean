import Solidity.Calculus.DecisionUIntFormula
import Solidity.Calculus.DecisionLeafEquality

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
