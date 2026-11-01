import Solidity.Calculus.DecisionNumericCoverage

/-! # Numeric logical bodies for the unchanged decision route
An intrinsic proof predicate on existing LFml, preserving optional/strict
arithmetic behavior. This is neither an alternate formula IR nor Residue.
-/
namespace Solidity.Decide

/-- Quantifier-free logical combinations of existing numeric uint terms. -/
inductive LFml.UIntQF {C : Contract} (P : Parameter → Prop) (E : EnvKey → Prop) : LFml C → Prop
  | tt : LFml.UIntQF P E .tt
  | eq {a b : LTm C (.val .uint)} : a.Num P E → b.Num P E → LFml.UIntQF P E (.eq a b)
  | not {φ : LFml C} : φ.UIntQF P E → LFml.UIntQF P E (.not φ)
  | and {φ ψ : LFml C} : φ.UIntQF P E → ψ.UIntQF P E → LFml.UIntQF P E (.and φ ψ)
  | imp {φ ψ : LFml C} : φ.UIntQF P E → ψ.UIntQF P E → LFml.UIntQF P E (.imp φ ψ)

theorem LFml.UIntQF.source {C : Contract} {P : Parameter → Prop} {E : EnvKey → Prop}
    {φ : LFml C} (h : φ.UIntQF P E) (c w : Bool) : φ.Src c w := by
  induction h with
  | tt => exact .tt
  | eq ha hb => exact .ofNums (numeric_source ha c w) (numeric_source hb c w)
  | not ha ih => exact .not ih
  | and ha hb iha ihb => exact .and iha ihb
  | imp ha hb iha ihb => exact .imp iha ihb

theorem LFml.UIntQF.parser {C : Contract} {P : Parameter → Prop} {E : EnvKey → Prop}
    {φ : LFml C} (h : φ.UIntQF P E) (c : Bool) : (φ.src? c).isSome = true := by
  induction h with
  | tt => rfl
  | eq ha hb => exact numeric_uint_eq_parser ha hb c
  | not ha ih => exact source_parser_not ih
  | and ha hb iha ihb => exact source_parser_and iha ihb
  | imp ha hb iha ihb => exact source_parser_imp iha ihb

theorem LFml.UIntQF.cut_identity {C : Contract} {P : Parameter → Prop} {E : EnvKey → Prop}
    {φ : LFml C} (h : φ.UIntQF P E) (prev : List (LFml C)) (start : Nat) :
    φ.cut prev start = ⟨φ, [], start⟩ := by
  induction h generalizing prev start with
  | tt => rfl
  | eq ha hb => exact numeric_eq_cut ha hb prev start
  | not ha ih => simp only [LFml.cut, ih]
  | and ha hb iha ihb | imp ha hb iha ihb =>
    simp only [LFml.cut, iha, ihb, List.append_nil]

theorem LFml.UIntQF.parameters {C : Contract} {P : Parameter → Prop} {E : EnvKey → Prop}
    {φ : LFml C} (h : φ.UIntQF P E) : ∀ q ∈ φ.parameters, P q := by
  induction h with
  | tt => intro q hq; cases hq
  | eq ha hb =>
    intro q hq
    rcases List.mem_append.mp hq with hqa | hqb
    · exact numeric_parameters ha q hqa
    · exact numeric_parameters hb q hqb
  | not ha ih => exact ih
  | and ha hb iha ihb | imp ha hb iha ihb =>
    intro q hq
    rcases List.mem_append.mp hq with hqa | hqb
    · exact iha q hqa
    · exact ihb q hqb

theorem LFml.UIntQF.conds {C : Contract} {P : Parameter → Prop} {E : EnvKey → Prop}
    {φ : LFml C} (h : φ.UIntQF P E) : φ.conds = 0 := by
  induction h with
  | tt => rfl
  | eq ha hb => simp only [LFml.conds, numeric_no_conds ha, numeric_no_conds hb, Nat.zero_add]
  | not ha ih => exact ih
  | and ha hb iha ihb | imp ha hb iha ihb => simp only [LFml.conds, iha, ihb, Nat.zero_add]

theorem LFml.UIntQF.condMax {C : Contract} {P : Parameter → Prop} {E : EnvKey → Prop}
    {φ : LFml C} (h : φ.UIntQF P E) : φ.condMax ≤ 2 := by
  induction h with
  | tt => exact Nat.zero_le 2
  | eq ha hb => simp only [LFml.condMax, numeric_no_conds ha, numeric_no_conds hb]; decide
  | not ha ih => exact ih
  | and ha hb iha ihb | imp ha hb iha ihb => exact Nat.max_le.mpr ⟨iha, ihb⟩

/-- Optional source equality expands entirely within the same numeric logical class. -/
theorem LFml.UIntQF.optEq {C : Contract} {P : Parameter → Prop} {E : EnvKey → Prop}
    {a b : LTm C (.val .uint)} (ha : a.Num P E) (hb : b.Num P E) :
    (LFml.optEq a b).UIntQF P E :=
  .and (.imp (.eq ha ha) (.imp (.eq hb hb) (.eq ha hb)))
    (.and (.imp (.eq ha ha) (.eq hb hb)) (.imp (.eq hb hb) (.eq ha ha)))

/-- Elimination preserves numeric logical shape and its exact atom predicates. -/
theorem LFml.UIntQF.elim {C : Contract} {P : Parameter → Prop} {E : EnvKey → Prop}
    {φ : LFml C} (h : φ.UIntQF P E) : φ.elim.UIntQF P E := by
  induction h with
  | tt => exact .tt
  | eq ha hb => exact .eq (numeric_elim ha) (numeric_elim hb)
  | not ha ih => exact .not ih
  | and ha hb iha ihb => exact .and iha ihb
  | imp ha hb iha ihb => exact .imp iha ihb

theorem LFml.UIntQF.condSimp {C : Contract} {P : Parameter → Prop} {E : EnvKey → Prop}
    {φ : LFml C} (h : φ.UIntQF P E) : φ.condSimp.UIntQF P E := by
  induction h with
  | tt => exact .tt
  | eq ha hb => exact .eq (numeric_condSimp ha) (numeric_condSimp hb)
  | not ha ih => exact .not ih
  | and ha hb iha ihb => exact .and iha ihb
  | imp ha hb iha ihb => exact .imp iha ihb

/-- No quantifier occurs in a numeric logical body, so pulling an implication is identity. -/
theorem LFml.UIntQF.pullImp {C : Contract} {P : Parameter → Prop} {E : EnvKey → Prop}
    {φ : LFml C} (h : φ.UIntQF P E) (χ : LFml C) : χ.pullImp φ = .imp χ φ := by
  cases h <;> rfl

theorem LFml.UIntQF.prenex_fixed {C : Contract} {P : Parameter → Prop} {E : EnvKey → Prop}
    {φ : LFml C} (h : φ.UIntQF P E) : φ.prenex = φ := by
  induction h with
  | tt | eq | not | and => rfl
  | imp ha hb iha ihb =>
    change _ = LFml.imp _ _
    rw [LFml.prenex, ihb, hb.pullImp]

/-- Actual preparation remains in the same logical body grammar. -/
theorem LFml.UIntQF.prepared {C : Contract} {P : Parameter → Prop} {E : EnvKey → Prop}
    {φ : LFml C} (h : φ.UIntQF P E) : φ.elim.condSimp.prenex.UIntQF P E := by
  have hp : φ.elim.condSimp.UIntQF P E := h.elim.condSimp
  rw [hp.prenex_fixed]
  exact hp

/-- Formula-specific numeric logical invariants discharge the original exact tests.
The sole size premise is on this actual body's structural node count. -/
theorem LFml.UIntQF.exact_tests {C : Contract} {ψ : LFml C}
    (h : ψ.UIntQF (fun q => q = ⟨.uint, 0⟩) (fun _ => False))
    (hn : ψ.nodes ≤ 511) :
    (LFml.all 0 .uint ψ).inExact = true ∧ (LFml.all 0 .uint ψ).exactBounded = true := by
  have hshape : ψ.allDepth = 0 ∧ ψ.stripAll = ([], ψ) := source_body_shape (h.source false true)
  have hparseStrip : (ψ.stripAll.2.src? true).isSome = true := by
    rw [hshape.2]
    exact h.parser true
  have hparams : ψ.parameters.all (fun q => decide (q ∈ [⟨.uint, 0⟩])) = true := by
    apply List.all_eq_true.mpr
    intro q hq
    simp only [decide_eq_true_eq]
    exact List.mem_singleton.mpr (h.parameters q hq)
  have hzero : (LFml.all 0 .uint ψ).conds = 0 := h.conds
  have hlift : (LFml.all 0 .uint ψ).liftCond condLiftFuel = .all 0 .uint ψ := by
    simpa only [LFml.condSimp_of_conds _ hzero] using
      LFml.liftCond_condSimp_of_conds condLiftFuel (.all 0 .uint ψ) hzero
  have hcut : ψ.cutAll = ψ := by simp only [LFml.cutAll, h.cut_identity]
  have hcond : ψ.condMax < condLiftFuel := by
    have hm : ψ.condMax ≤ 2 := h.condMax
    have hc : 2 < condLiftFuel := by decide
    exact Nat.lt_of_le_of_lt hm hc
  constructor
  · simp only [LFml.inExact, LFml.allDepth, LFml.stripAll, hshape.1, hshape.2,
      hparseStrip, hparams, hcond, decide_true, Bool.and_true]
    rfl
  · simp only [LFml.exactBounded, hlift, LFml.stripAll, hshape.2, hcut,
      hn, decide_true, Bool.and_true]

/-- A source structural bound for the supported quantifier-free grammar only.
Unsupported constructors return zero; this function is not an admission test. -/
def _root_.Solidity.Fml.uintQFWeight {C : Contract} {Γ : Ctx} (φ : Fml C Γ) : Nat := by
  apply @Fml.casesOn C (fun Γ φ => Nat) Γ φ
  · intro Γ; exact 1
  · intro Γ p a b; exact 7 * (a.size + b.size) + 13
  · intros; exact 0
  · intro Γ φ; exact φ.uintQFWeight + 1
  · intro Γ φ ψ; exact φ.uintQFWeight + ψ.uintQFWeight + 1
  · intro Γ φ ψ; exact φ.uintQFWeight + ψ.uintQFWeight + 1
  all_goals intros; exact 0
termination_by structural φ

theorem uintEq_logic {C : Contract} {Γ : Ctx} {P : Parameter → Prop} {E : EnvKey → Prop}
    {a b : Tm C Γ (.val .uint)} (ha : a.UIntLinear) (hb : b.UIntLinear)
    {x y : LTm C (.val .uint)} (hx : x.Num P E) (hy : y.Num P E) :
    (Fml.eqAt true a b x y).UIntQF P E := by
  unfold Fml.eqAt
  rw [uintLinear_agrees ha, uintLinear_agrees hb]
  simp only [Bool.true_and, if_true]
  split
  · exact .eq hx hy
  · exact .optEq hx hy

theorem uintEq_fixed {C : Contract} {Γ : Ctx}
    {a b : Tm C Γ (.val .uint)} (ha : a.UIntLinear) (hb : b.UIntLinear)
    {x y : LTm C (.val .uint)}
    (hEx : (x.elim : LTm C (.val .uint)) = x) (hEy : (y.elim : LTm C (.val .uint)) = y)
    (hCx : x.condSimp = x) (hCy : y.condSimp = y) :
    (Fml.eqAt true a b x y).elim = Fml.eqAt true a b x y ∧
      (Fml.eqAt true a b x y).condSimp = Fml.eqAt true a b x y := by
  unfold Fml.eqAt
  rw [uintLinear_agrees ha, uintLinear_agrees hb]
  simp only [Bool.true_and, if_true]
  split <;> simp only [LFml.elim, LFml.condSimp, LFml.optEq, hEx, hEy, hCx, hCy,
    and_self]

/-- Both real source polarities produce one numeric logical body, bounded by
original source syntax. Optional equality copies and every connective are counted. -/
theorem qfUIntLinear_prefix_sourceBound {C : Contract}
    {φ : Fml C [.val .uint]} (h : φ.QFUIntLinear) :
    ∃ ψ : LFml C,
      φ.toLS true ((SymS.init (C := C)).pushQ .uint) = some ψ ∧
      φ.toLS false ((SymS.init (C := C)).pushQ .uint) = some ψ ∧
      ψ.UIntQF (fun q => q = ⟨.uint, 0⟩) (fun _ => False) ∧
      ψ.elim = ψ ∧ ψ.condSimp = ψ ∧ ψ.nodes ≤ φ.uintQFWeight := by
  induction h with
  | tt => exact ⟨.tt, rfl, rfl, .tt, rfl, rfl, Nat.le_refl 1⟩
  | @eq a b ha hb =>
    obtain ⟨x, hx, hNx, hEx, hCx, hSx⟩ := uintLinear_prefix_sourceBound ha
    obtain ⟨y, hy, hNy, hEy, hCy, hSy⟩ := uintLinear_prefix_sourceBound hb
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

/-- A source-weight bound derives the actual unchanged 511-node body test.
Normalization/source-reducer traversal is a separate obligation for general bodies. -/
theorem qfUIntLinear_formula_bound {C : Contract} {φ : Fml C [.val .uint]}
    (h : φ.QFUIntLinear) (hw : φ.uintQFWeight ≤ 511) :
    ∃ ψ : LFml C,
      φ.toLS true ((SymS.init (C := C)).pushQ .uint) = some ψ ∧
      φ.toLS false ((SymS.init (C := C)).pushQ .uint) = some ψ ∧
      ψ.elim.condSimp.prenex = ψ ∧ ψ.nodes ≤ 511 ∧
      (LFml.all 0 .uint ψ).inExact = true ∧ (LFml.all 0 .uint ψ).exactBounded = true := by
  obtain ⟨ψ, hp, hn, hs, he, hc, hb⟩ := qfUIntLinear_prefix_sourceBound h
  have hnodes : ψ.nodes ≤ 511 := Nat.le_trans hb hw
  have hfixed : ψ.elim.condSimp.prenex = ψ := by rw [he, hc, hs.prenex_fixed]
  exact ⟨ψ, hp, hn, hfixed, hnodes, hs.exact_tests hnodes⟩

/-- Every positive uint prefix of this logical source grammar is admitted by
both frozen source filters, independently of normalization/coverage tests. -/
theorem qfUIntPrefix_inTarget {C : Contract} (name : Var) {φ : Fml C [.val .uint]}
    (h : φ.QFUIntLinear) (w : Waivers) : (Fml.all name .uint φ).inTarget w = true := by
  have ht : (Fml.all name .uint φ).target w true false = true := by
    cases hr : φ.readsAt [0] <;>
      simp only [Fml.target, List.length_nil, hr] <;>
      exact qfUIntLinear_target h w true false
  unfold Fml.inTarget
  rw [ht]
  simp only [Fml.mapKeys, qfUIntLinear_mapKeys h, Fml.negPairUnread,
    qfUIntLinear_negPairUnread h, Bool.not_true, Bool.false_and, Bool.false_or]
  rfl

theorem qfUIntPrefix_hashFree {C : Contract} (name : Var) {φ : Fml C [.val .uint]}
    (h : φ.QFUIntLinear) : (Fml.all name .uint φ).hasHash = false := by
  change φ.hasHash = false
  induction h with
  | tt => rfl
  | eq ha hb => simp only [Fml.hasHash, uintLinear_hashFree ha, uintLinear_hashFree hb, Bool.false_or]
  | not ha ih => exact ih
  | and ha hb iha ihb | imp ha hb iha ihb => simp only [Fml.hasHash, iha, ihb, Bool.false_or]

/-- A conditional integration interface: callers supply the actual checked
source-to-leaf equation, never an assumed producer theorem or validity oracle. -/
theorem qfUIntLogic_Covered_of_leaf {C : Contract} {φ : Fml C []} {ψ : LFml C}
    (h : ψ.UIntQF (fun q => q = ⟨.uint, 0⟩) (fun _ => False)) (hn : ψ.nodes ≤ 511)
    (hl : leafOf? φ = some (.all 0 .uint ψ)) : φ.Covered = true := by
  obtain ⟨hi, hb⟩ := h.exact_tests hn
  have hin : φ.inExact = true := by simpa only [Fml.inExact, hl] using hi
  have hbound : φ.exactBounded = true := by simpa only [Fml.exactBounded, hl] using hb
  simp only [Fml.Covered, Fml.CoveredA, hin, hbound, Bool.true_and, Bool.true_or]

end Solidity.Decide
