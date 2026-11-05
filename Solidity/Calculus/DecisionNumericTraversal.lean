import Solidity.Calculus.DecisionNumericLogic

/-! # Concrete source traversal for numeric logical formulas
Prove facts about the existing fuelled source reducer. No source/compiler API,
fuel or supported-profile change is made. Normalizer traversal stays separate.
-/
namespace Solidity.Decide

theorem qfUIntLinear_weight_positive {C : Contract} {Γ : Ctx} {φ : Fml C Γ}
    (h : φ.QFUIntLinear) : 0 < φ.uintQFWeight := by
  cases h with
  | tt => exact Nat.zero_lt_succ 0
  | eq => change 0 < 7 * (_ + _) + 13; omega
  | not => change 0 < _ + 1; omega
  | and | imp => change 0 < _ + _ + 1; omega

/-- Equal-polarity source translations produce an actual directional certificate. -/
theorem directional_certificate_of_polarities {C : Contract} {Γ : Ctx}
    (ρ : SymS C Γ) (φ : Fml C Γ) (ψ : LFml C)
    (hp : φ.toLS true ρ = some ψ) (hn : φ.toLS false ρ = some ψ) :
    ∃ r : ExactAt ρ φ, ExactAt.directional? ρ φ = some r ∧ r.leaf = ψ := by
  have hm : (ExactAt.directional? ρ φ).map (·.leaf) = some ψ :=
    directional_leaf_of_polarities ρ φ ψ hp hn
  cases hr : ExactAt.directional? ρ φ with
  | none => rw [hr] at hm; cases hm
  | some r =>
    rw [hr] at hm
    exact ⟨r, rfl, Option.some.inj hm⟩

/-- The source-derived structural weight bounds real reducer traversal fuel.
Both source polarities and the exact returned certificate leaf are preserved. -/
theorem qfUIntLinear_exact_source {C : Contract} (fuel : Nat)
    {φ : Fml C [.val .uint]} (h : φ.QFUIntLinear) (hw : φ.uintQFWeight ≤ fuel) :
    ∃ (r : ExactAt ((SymS.init (C := C)).pushQ .uint) φ) (ψ : LFml C),
      ExactAt.ofFormula? fuel ((SymS.init (C := C)).pushQ .uint) φ = some r ∧
      r.leaf = ψ ∧ φ.toLS true ((SymS.init (C := C)).pushQ .uint) = some ψ ∧
      φ.toLS false ((SymS.init (C := C)).pushQ .uint) = some ψ := by
  induction fuel generalizing φ with
  | zero => exact False.elim (Nat.not_lt_of_ge hw (qfUIntLinear_weight_positive h))
  | succ fuel ih =>
    cases h with
    | tt =>
      obtain ⟨r, hr, hl⟩ := directional_certificate_of_polarities
        ((SymS.init (C := C)).pushQ .uint) .tt .tt rfl rfl
      exact ⟨r, .tt, hr, hl, rfl, rfl⟩
    | @eq a b ha hb =>
      obtain ⟨ψ, hp, hn, hs, he, hc, hbnd⟩ := qfUIntLinear_prefix_sourceBound (.eq ha hb)
      obtain ⟨r, hr, hl⟩ := directional_certificate_of_polarities
        ((SymS.init (C := C)).pushQ .uint) (.eq a b) ψ hp hn
      refine ⟨r, ψ, ?_, hl, hp, hn⟩
      change (ExactAt.directional? _ (.eq a b)).orElse _ = some r
      rw [hr]
      rfl
    | @not φ hφ =>
      have hφw : φ.uintQFWeight ≤ fuel := by
        change φ.uintQFWeight + 1 ≤ fuel + 1 at hw
        omega
      obtain ⟨r, ψ, hr, hl, hp, hn⟩ := ih hφ hφw
      refine ⟨ExactAt.not r, .not ψ, ?_, congrArg LFml.not hl, ?_, ?_⟩
      · change (ExactAt.ofFormula? fuel _ φ).map ExactAt.not = some (ExactAt.not r)
        rw [hr]
        rfl
      · change (φ.toLS false _).map LFml.not = some (.not ψ)
        rw [hn]
        rfl
      · change (φ.toLS true _).map LFml.not = some (.not ψ)
        rw [hp]
        rfl
    | @and φ χ hφ hχ =>
      have hφw : φ.uintQFWeight ≤ fuel := by
        change φ.uintQFWeight + χ.uintQFWeight + 1 ≤ fuel + 1 at hw
        omega
      have hχw : χ.uintQFWeight ≤ fuel := by
        change φ.uintQFWeight + χ.uintQFWeight + 1 ≤ fuel + 1 at hw
        omega
      obtain ⟨r, ψ, hr, hl, hp, hn⟩ := ih hφ hφw
      obtain ⟨s, θ, kr, kl, kp, kn⟩ := ih hχ hχw
      refine ⟨ExactAt.and r s, .and ψ θ, ?_, ?_, ?_, ?_⟩
      · change (ExactAt.ofFormula? fuel _ φ).bind (fun u =>
          (ExactAt.ofFormula? fuel _ χ).bind (fun v => some (ExactAt.and u v))) = _
        rw [hr, kr]
        rfl
      · simp only [ExactAt.and, hl, kl]
      · change (φ.toLS true _).bind (fun u => (χ.toLS true _).map (LFml.and u)) = _
        rw [hp, kp]
        rfl
      · change (φ.toLS false _).bind (fun u => (χ.toLS false _).map (LFml.and u)) = _
        rw [hn, kn]
        rfl
    | @imp φ χ hφ hχ =>
      have hφw : φ.uintQFWeight ≤ fuel := by
        change φ.uintQFWeight + χ.uintQFWeight + 1 ≤ fuel + 1 at hw
        omega
      have hχw : χ.uintQFWeight ≤ fuel := by
        change φ.uintQFWeight + χ.uintQFWeight + 1 ≤ fuel + 1 at hw
        omega
      obtain ⟨r, ψ, hr, hl, hp, hn⟩ := ih hφ hφw
      obtain ⟨s, θ, kr, kl, kp, kn⟩ := ih hχ hχw
      refine ⟨ExactAt.imp r s, .imp ψ θ, ?_, ?_, ?_, ?_⟩
      · change (ExactAt.ofFormula? fuel _ φ).bind (fun u =>
          (ExactAt.ofFormula? fuel _ χ).bind (fun v => some (ExactAt.imp u v))) = _
        rw [hr, kr]
        rfl
      · simp only [ExactAt.imp, hl, kl]
      · change (φ.toLS false _).bind (fun u => (χ.toLS true _).map (LFml.imp u)) = _
        rw [hn, kp]
        rfl
      · change (φ.toLS true _).bind (fun u => (χ.toLS false _).map (LFml.imp u)) = _
        rw [hp, kn]
        rfl

/-- The unchanged 2048-step public source reducer handles the positive prefix.
The source-derived weight proves its body traversal fits; no oracle substitutes. -/
theorem qfUIntPrefix_sourceReduction {C : Contract} (name : Var)
    {φ : Fml C [.val .uint]} (h : φ.QFUIntLinear) (hw : φ.uintQFWeight ≤ 2047) :
    ∃ ψ : LFml C,
      (sourceReduction? (.all name .uint φ)).map (·.leaf) = some (.all 0 .uint ψ) ∧
      φ.toLS true ((SymS.init (C := C)).pushQ .uint) = some ψ ∧
      φ.toLS false ((SymS.init (C := C)).pushQ .uint) = some ψ := by
  obtain ⟨r, ψ, hr, hl, hp, hn⟩ := qfUIntLinear_exact_source 2047 h hw
  refine ⟨ψ, ?_, hp, hn⟩
  simp only [sourceReduction?, ExactAt.ofFormula?, hr, Option.map_some,
    Option.bind_eq_bind, Option.pure_def, Option.bind_some, ExactAt.all, hl]
  rfl

/-- Actual source reduction reaches the numeric logical shape and source bound.
Only program normalization, which precedes this reducer, remains separate. -/
theorem qfUIntPrefix_source_coverageFacts {C : Contract} (name : Var)
    {φ : Fml C [.val .uint]} (h : φ.QFUIntLinear) (hw : φ.uintQFWeight ≤ 511) :
    ∃ ψ : LFml C,
      (sourceReduction? (.all name .uint φ)).map (·.leaf) = some (.all 0 .uint ψ) ∧
      ψ.UIntQF (fun q => q = ⟨.uint, 0⟩) (fun _ => False) ∧
      ψ.elim.condSimp.prenex = ψ ∧ ψ.nodes ≤ 511 := by
  obtain ⟨ψ, hr, hp, hn⟩ := qfUIntPrefix_sourceReduction name h (by omega)
  obtain ⟨θ, kp, kn, hs, he, hc, hb⟩ := qfUIntLinear_prefix_sourceBound h
  have ht : θ = ψ := Option.some.inj (kp.symm.trans hp)
  subst θ
  refine ⟨ψ, hr, hs, ?_, Nat.le_trans hb hw⟩
  rw [he, hc, hs.prenex_fixed]

end Solidity.Decide
