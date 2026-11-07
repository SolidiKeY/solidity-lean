import Solidity.Calculus.DecisionNumericFlatten
import Solidity.Calculus.DecisionNumericGroundSource

/-! # Actual source-to-flattener numeric stages
Compose existing normalization, source reduction and structural flattening.
This does not claim later compiler totality or enlarge global coverage.
-/
namespace Solidity.Decide

/-- Closed source syntax reaches its actual numeric leaf within unchanged2048
source traversal, independently of the later511-node coverage criterion. -/
theorem qfUIntGround_leaf_stage {C : Contract} {φ : Fml C []}
    (h : φ.QFUIntLinear) (hw : φ.uintQFWeight ≤ 2048) :
    ∃ ψ : LFml C, leafOf? φ = some ψ ∧
      ψ.UIntQF (fun _ => False) (fun _ => False) ∧ ψ.nodes ≤ φ.uintQFWeight := by
  obtain ⟨d, hd, hg, hs⟩ := qfUIntLinear_normalization 2048 h hw
  obtain ⟨r, ψ, hr, hl, hp, hn⟩ := qfUIntGround_exact_source 2048 hg (by omega)
  obtain ⟨θ, kp, kn, ht, he, hc, hb⟩ := qfUIntLinear_ground_sourceBound hg
  have heq : θ = ψ := Option.some.inj (kp.symm.trans hp)
  subst θ
  have hsource : (sourceReduction? d.formula).map (·.leaf) = some ψ := by
    simp only [sourceReduction?, hr, Option.bind_eq_bind, Option.pure_def,
      Option.bind_some, Option.map_some, hl]
  have hnorm : (ProgramNormalization.ofFormula? 2048 φ).map (·.formula) = some d.formula := by
    rw [hd]
    rfl
  have hprep : ψ.elim.condSimp.prenex = ψ := by rw [he, hc, ht.prenex_fixed]
  have hleaf : leafOf? φ = some ψ.elim.condSimp.prenex :=
    leafOf_of_normalized_to φ d.formula ψ hnorm hsource
  rw [hprep] at hleaf
  exact ⟨ψ, hleaf, ht, Nat.le_trans hb hs⟩

/-- The positive source binder and actual normalized body reach the real leaf. -/
theorem qfUIntPrefix_leaf_stage {C : Contract} (name : Var)
    {φ : Fml C [.val .uint]} (h : φ.QFUIntLinear) (hw : φ.uintQFWeight ≤ 2047) :
    ∃ ψ : LFml C, leafOf? (.all name .uint φ) = some (.all 0 .uint ψ) ∧
      ψ.UIntQF (fun q => q = ⟨.uint, 0⟩) (fun _ => False) ∧ ψ.nodes ≤ φ.uintQFWeight := by
  obtain ⟨χ, hn, hg, hs⟩ := qfUIntPrefix_normalization_sourceFuel name h hw
  obtain ⟨ψ, hr, hp, hk⟩ := qfUIntPrefix_sourceReduction name hg (by omega)
  obtain ⟨θ, kp, kn, ht, he, hc, hb⟩ := qfUIntLinear_prefix_sourceBound hg
  have heq : θ = ψ := Option.some.inj (kp.symm.trans hp)
  subst θ
  have hprep : ψ.elim.condSimp.prenex = ψ := by rw [he, hc, ht.prenex_fixed]
  have hleaf : leafOf? (.all name .uint φ) =
      some (LFml.all 0 .uint ψ).elim.condSimp.prenex :=
    leafOf_of_normalized_to (.all name .uint φ) (.all name .uint χ) (.all 0 .uint ψ) hn hr
  have hleaf' : leafOf? (.all name .uint φ) = some (.all 0 .uint ψ) := by
    simpa only [LFml.elim, LFml.condSimp, LFml.prenex, hprep] using hleaf
  exact ⟨ψ, hleaf', ht, Nat.le_trans hb hs⟩

/-- All certificates are actual existing producer results; no supplied leaf,
normalizer equation or future compiler premise appears. -/
theorem qfUIntGround_flatten_stage {C : Contract} {φ : Fml C []}
    (h : φ.QFUIntLinear) (hw : φ.uintQFWeight ≤ 2048) (start : Nat) :
    ∃ ψ : LFml C, leafOf? φ = some ψ ∧
      ψ.UIntQF (fun _ => False) (fun _ => False) ∧ ψ.nodes ≤ φ.uintQFWeight ∧
      ∃ a : FlattenedFormula ψ start, flattenFormulaAt? ψ.nodes start ψ = some a ∧
        a.formula = ψ ∧ a.reads = [] := by
  obtain ⟨ψ, hl, hg, hn⟩ := qfUIntGround_leaf_stage h hw
  obtain ⟨a, ha, hf, hr⟩ := numeric_formula_flattenAt_nodes hg start
  exact ⟨ψ, hl, hg, hn, a, ha, hf, hr⟩

theorem qfUIntPrefix_flatten_stage {C : Contract} (name : Var)
    {φ : Fml C [.val .uint]} (h : φ.QFUIntLinear) (hw : φ.uintQFWeight ≤ 2047) (start : Nat) :
    ∃ ψ : LFml C, leafOf? (.all name .uint φ) = some (.all 0 .uint ψ) ∧
      ψ.UIntQF (fun q => q = ⟨.uint, 0⟩) (fun _ => False) ∧
      ψ.nodes ≤ φ.uintQFWeight ∧
      ∃ a : FlattenedFormula ψ start, flattenFormulaAt? ψ.nodes start ψ = some a ∧
        a.formula = ψ ∧ a.reads = [] := by
  obtain ⟨ψ, hl, hg, hn⟩ := qfUIntPrefix_leaf_stage name h hw
  obtain ⟨a, ha, hf, hr⟩ := numeric_formula_flattenAt_nodes hg start
  exact ⟨ψ, hl, hg, hn, a, ha, hf, hr⟩

end Solidity.Decide
