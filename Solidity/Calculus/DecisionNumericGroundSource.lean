import Solidity.Calculus.DecisionNumericGround
import Solidity.Calculus.DecisionNumericNormalization

/-! # Closed numeric source discovery
Proofs follow the existing reducer and normalizer on intrinsic source syntax.
The source-derived weight is sufficient for unchanged traversal/node bounds.
-/
namespace Solidity.Decide

/-- Closed numeric source translation carries its actual structural bound. -/
theorem qfUIntLinear_ground_sourceBound {C : Contract}
    {φ : Fml C []} (h : φ.QFUIntLinear) :
    ∃ ψ : LFml C,
      φ.toLS true (SymS.init (C := C)) = some ψ ∧
      φ.toLS false (SymS.init (C := C)) = some ψ ∧
      ψ.UIntQF (fun _ => False) (fun _ => False) ∧
      ψ.elim = ψ ∧ ψ.condSimp = ψ ∧ ψ.nodes ≤ φ.uintQFWeight := by
  induction h with
  | tt => exact ⟨.tt, rfl, rfl, .tt, rfl, rfl, Nat.le_refl 1⟩
  | @eq a b ha hb =>
    obtain ⟨x, hx, hNx, hEx, hCx, hSx⟩ := uintLinear_ground_sourceBound ha
    obtain ⟨y, hy, hNy, hEy, hCy, hSy⟩ := uintLinear_ground_sourceBound hb
    rw [toLT_eq_toL_of_agree a _ (uintLinear_agrees ha)] at hx
    rw [toLT_eq_toL_of_agree b _ (uintLinear_agrees hb)] at hy
    have hfix : (Fml.eqAt true a b x y).elim = Fml.eqAt true a b x y ∧
        (Fml.eqAt true a b x y).condSimp = Fml.eqAt true a b x y :=
      uintEq_fixed ha hb hEx hEy hCx hCy
    refine ⟨Fml.eqAt true a b x y, ?_, ?_, uintEq_logic ha hb hNx hNy,
      hfix.1, hfix.2, ?_⟩
    · change (a.toL _).bind (fun u => (b.toL _).map (fun v => Fml.eqAt true a b u v)) = _
      rw [hx, hy]
      rfl
    · change (a.toL _).bind (fun u => (b.toL _).map (fun v => Fml.eqAt false a b u v)) = _
      rw [hx, hy]
      exact congrArg some (uintLinear_eqAt_polarity ha hb x y false)
    · have hbnd : (Fml.eqAt true a b x y).elim.condSimp.prenex.nodes ≤
          7 * x.nodes + 7 * y.nodes + 13 := uintEq_prepared_nodes_le ha hb hEx hEy hCx hCy
      rw [hfix.1, hfix.2, (uintEq_logic ha hb hNx hNy).prenex_fixed] at hbnd
      change _ ≤ 7 * (a.size + b.size) + 13
      omega
  | @not φ h ih =>
    obtain ⟨ψ, hp, hn, hs, he, hc, hb⟩ := ih
    refine ⟨.not ψ, ?_, ?_, .not hs, congrArg LFml.not he, congrArg LFml.not hc, ?_⟩
    · change (φ.toLS false _).map LFml.not = _
      rw [hn]
      rfl
    · change (φ.toLS true _).map LFml.not = _
      rw [hp]
      rfl
    · change ψ.nodes + 1 ≤ φ.uintQFWeight + 1
      omega
  | @and φ χ hφ hχ ihφ ihχ =>
    obtain ⟨ψ, hp, hn, hs, he, hc, hb⟩ := ihφ
    obtain ⟨θ, kp, kn, ks, ke, kc, kb⟩ := ihχ
    refine ⟨.and ψ θ, ?_, ?_, .and hs ks, ?_, ?_, ?_⟩
    · change (φ.toLS true _).bind (fun u => (χ.toLS true _).map (LFml.and u)) = _
      rw [hp, kp]
      rfl
    · change (φ.toLS false _).bind (fun u => (χ.toLS false _).map (LFml.and u)) = _
      rw [hn, kn]
      rfl
    · simp only [LFml.elim, he, ke]
    · simp only [LFml.condSimp, hc, kc]
    · change ψ.nodes + θ.nodes + 1 ≤ φ.uintQFWeight + χ.uintQFWeight + 1
      omega
  | @imp φ χ hφ hχ ihφ ihχ =>
    obtain ⟨ψ, hp, hn, hs, he, hc, hb⟩ := ihφ
    obtain ⟨θ, kp, kn, ks, ke, kc, kb⟩ := ihχ
    refine ⟨.imp ψ θ, ?_, ?_, .imp hs ks, ?_, ?_, ?_⟩
    · change (φ.toLS false _).bind (fun u => (χ.toLS true _).map (LFml.imp u)) = _
      rw [hn, kp]
      rfl
    · change (φ.toLS true _).bind (fun u => (χ.toLS false _).map (LFml.imp u)) = _
      rw [hp, kn]
      rfl
    · simp only [LFml.elim, he, ke]
    · simp only [LFml.condSimp, hc, kc]
    · change ψ.nodes + θ.nodes + 1 ≤ φ.uintQFWeight + χ.uintQFWeight + 1
      omega


/-- Actual reducer traversal; no supplied leaf equation or oracle. -/
theorem qfUIntGround_exact_source {C : Contract} (fuel : Nat)
    {φ : Fml C []} (h : φ.QFUIntLinear) (hw : φ.uintQFWeight ≤ fuel) :
    ∃ (r : ExactAt (SymS.init (C := C)) φ) (ψ : LFml C),
      ExactAt.ofFormula? fuel (SymS.init (C := C)) φ = some r ∧
      r.leaf = ψ ∧ φ.toLS true (SymS.init (C := C)) = some ψ ∧
      φ.toLS false (SymS.init (C := C)) = some ψ := by
  induction fuel generalizing φ with
  | zero => exact False.elim (Nat.not_lt_of_ge hw (qfUIntLinear_weight_positive h))
  | succ fuel ih =>
    cases h with
    | tt =>
      obtain ⟨r, hr, hl⟩ := directional_certificate_of_polarities
        (SymS.init (C := C)) .tt .tt rfl rfl
      exact ⟨r, .tt, hr, hl, rfl, rfl⟩
    | @eq a b ha hb =>
      obtain ⟨ψ, hp, hn, hs, he, hc, hbnd⟩ := qfUIntLinear_ground_sourceBound (.eq ha hb)
      obtain ⟨r, hr, hl⟩ := directional_certificate_of_polarities
        (SymS.init (C := C)) (.eq a b) ψ hp hn
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


/-- Actual source reduction and preparation for the zero-prefix case. -/
theorem qfUIntGround_source_coverageFacts {C : Contract} {φ : Fml C []}
    (h : φ.QFUIntLinear) (hw : φ.uintQFWeight ≤ 511) :
    ∃ ψ : LFml C, (sourceReduction? φ).map (·.leaf) = some ψ ∧
      ψ.UIntQF (fun _ => False) (fun _ => False) ∧
      ψ.elim.condSimp.prenex = ψ ∧ ψ.nodes ≤ 511 := by
  obtain ⟨r, ψ, hr, hl, hp, hn⟩ := qfUIntGround_exact_source 2048 h (by omega)
  obtain ⟨θ, kp, kn, hs, he, hc, hb⟩ := qfUIntLinear_ground_sourceBound h
  have ht : θ = ψ := Option.some.inj (kp.symm.trans hp)
  subst θ
  refine ⟨ψ, ?_, hs, ?_, Nat.le_trans hb hw⟩
  · simp only [sourceReduction?, hr, Option.bind_eq_bind, Option.pure_def, Option.bind_some, Option.map_some, hl]
  · rw [he, hc, hs.prenex_fixed]

/-- Syntax and a formula-derived weight suffice for real global coverage. -/
theorem qfUIntGround_logic_Covered {C : Contract} {φ : Fml C []}
    (h : φ.QFUIntLinear) (hw : φ.uintQFWeight ≤ 511) : φ.Covered = true := by
  obtain ⟨d, hd, hg, hs⟩ := qfUIntLinear_normalization 2048 h (by omega)
  have hc : d.formula.uintQFWeight ≤ 511 := Nat.le_trans hs hw
  obtain ⟨ψ, hr, hψ, hp, hb⟩ := qfUIntGround_source_coverageFacts hg hc
  have hn : (ProgramNormalization.ofFormula? 2048 φ).map (·.formula) = some d.formula := by
    rw [hd]
    rfl
  have hl : leafOf? φ = some ψ.elim.condSimp.prenex :=
    leafOf_of_normalized_to φ d.formula ψ hn hr
  rw [hp] at hl
  exact qfUIntGround_Covered_of_leaf hψ hb hl

/-- Source syntax excludes hashes without strengthening their semantic premise. -/
theorem qfUIntGround_hashFree {C : Contract} {φ : Fml C []}
    (h : φ.QFUIntLinear) : φ.hasHash = false := by
  induction h with
  | tt => rfl
  | eq ha hb => simp only [Fml.hasHash, uintLinear_hashFree ha, uintLinear_hashFree hb, Bool.false_or]
  | not ha ih => exact ih
  | and ha hb iha ihb | imp ha hb iha ihb => simp only [Fml.hasHash, iha, ihb, Bool.false_or]

/-- A precise inhabited source boundary, not a revision of either predicate. -/
theorem qfUIntGround_logic_boundary {C : Contract} (w : Waivers) {φ : Fml C []}
    (h : φ.QFUIntLinear) (hw : φ.uintQFWeight ≤ 511) :
    φ.inTarget w = true ∧ φ.Covered = true ∧ φ.hasHash = false :=
  ⟨qfUIntLinear_inTarget h w, qfUIntGround_logic_Covered h hw, qfUIntGround_hashFree h⟩

theorem qfUIntGround_logic_answered {C : Contract} {φ : Fml C []}
    (h : φ.QFUIntLinear) (hw : φ.uintQFWeight ≤ 511) : decideGoal φ ≠ .unknown :=
  decideGoal_complete (qfUIntGround_logic_Covered h hw) (qfUIntGround_hashFree h)

/-- The actual verdict is certified under the unchanged holdsH hash interface. -/
theorem qfUIntGround_logic_certified {C : Contract} {φ : Fml C []}
    (h : φ.QFUIntLinear) (hw : φ.uintQFWeight ≤ 511) :
    (decideGoal φ = .proved ∧ Fml.ValidH φ) ∨
      ∃ σ : State C [], decideGoal φ = .refuted σ ∧ ¬ Fml.holdsH σ φ := by
  have hd : decideGoal φ ≠ .unknown := qfUIntGround_logic_answered h hw
  cases he : decideGoal φ with
  | proved => exact Or.inl ⟨rfl, decideGoal_sound he⟩
  | refuted σ => exact Or.inr ⟨σ, rfl, decideGoal_refutes he⟩
  | unknown => exact False.elim (hd he)

end Solidity.Decide
