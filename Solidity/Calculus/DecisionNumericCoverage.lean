import Solidity.Calculus.DecisionNumericBounds

/-!
# Numeric source coverage facts

Recognizer, cut and lift facts are proved against the existing functions.
No resource budget, source predicate or decision default is changed.
-/
namespace Solidity.Decide

/-- The existing numeric recognizer accepts Num at either conditional flag. -/
theorem numeric_src_parser {C : Contract} {P : Parameter → Prop} {E : EnvKey → Prop}
    {p : PrimTy} {t : LTm C (.val p)} (h : t.Num P E) (c : Bool) :
    (t.src? c .num).isSome = true := by
  induction h with
  | var k hk => rfl
  | @lit p v => cases p <;> rfl
  | env e he => rfl
  | err => rfl
  | @add p h a b ha hb iha ihb | @sub p h a b ha hb iha ihb =>
    obtain ⟨⟨u⟩, hu⟩ := Option.isSome_iff_exists.mp iha
    obtain ⟨⟨v⟩, hv⟩ := Option.isSome_iff_exists.mp ihb
    show (Option.bind (a.src? c .num) _).isSome = true
    rw [hu]
    show (Option.bind (b.src? c .num) _).isSome = true
    rw [hv]
    rfl
  | @mulL p h v b hb ihb =>
    show (LTm.mulSrc? h (.app0 (.lit v)) b _ _).isSome = true
    exact LTm.mulSrc?_left h v b _ _ ihb
  | @mulR p h a v ha iha =>
    show (LTm.mulSrc? h a (.app0 (.lit v)) _ _).isSome = true
    exact LTm.mulSrc?_right h a v _ _ iha (by cases p <;> rfl)
  | @neg h a ha iha | @bnot h a ha iha =>
    obtain ⟨⟨u⟩, hu⟩ := Option.isSome_iff_exists.mp iha
    show ((a.src? c .num).map _).isSome = true
    rw [hu]
    rfl
  | @seq q p d a hd ha ihd iha =>
    obtain ⟨⟨u⟩, hu⟩ := Option.isSome_iff_exists.mp ihd
    obtain ⟨⟨v⟩, hv⟩ := Option.isSome_iff_exists.mp iha
    show (Option.bind (d.src? c .num) _).isSome = true
    rw [hu]
    show (Option.bind (a.src? c .num) _).isSome = true
    rw [hv]
    rfl

/-- Cutting numeric terms introduces no definition or fresh atom and preserves the term. -/
theorem numeric_cut_identity {C : Contract} {P : Parameter → Prop} {E : EnvKey → Prop}
    {p : PrimTy} {t : LTm C (.val p)} (h : t.Num P E)
    (prev : List (LFml C)) (start : Nat) : t.cut prev start = ⟨t, [], start⟩ := by
  induction h generalizing prev start with
  | var k hk => rfl
  | lit v => rfl
  | env e he => rfl
  | err => rfl
  | add h ha hb iha ihb | sub h ha hb iha ihb =>
    simp only [LTm.cut, iha, ihb, cut2, List.append_nil]
  | mulL h v ha iha | mulR h v ha iha =>
    simp only [LTm.cut, iha, cut2, List.append_nil]
  | neg h ha iha | bnot h ha iha =>
    simp only [LTm.cut, iha, cut1]
  | seq hd ha ihd iha =>
    simp only [LTm.cut, ihd, iha, List.append_nil]

/-- Numeric uint equality is accepted at either recognizer flag. -/
theorem numeric_uint_eq_parser {C : Contract} {P : Parameter → Prop} {E : EnvKey → Prop}
    {x y : LTm C (.val .uint)} (hx : x.Num P E) (hy : y.Num P E) (c : Bool) :
    ((LFml.eq x y).src? c).isSome = true := by
  obtain ⟨⟨u⟩, hu⟩ := Option.isSome_iff_exists.mp (numeric_src_parser hx c)
  obtain ⟨⟨v⟩, hv⟩ := Option.isSome_iff_exists.mp (numeric_src_parser hy c)
  show (Option.bind (x.src? c .num) _).isSome = true
  rw [hu]
  show (Option.bind (y.src? c .num) _).isSome = true
  rw [hv]
  rfl

/-- Parsing conjunction requires only successful parsing of its operands. -/
theorem source_parser_and {C : Contract} {φ ψ : LFml C} {c : Bool}
    (hφ : (φ.src? c).isSome = true) (hψ : (ψ.src? c).isSome = true) :
    ((LFml.and φ ψ).src? c).isSome = true := by
  obtain ⟨⟨u⟩, hu⟩ := Option.isSome_iff_exists.mp hφ
  obtain ⟨⟨v⟩, hv⟩ := Option.isSome_iff_exists.mp hψ
  show (Option.bind (φ.src? c) _).isSome = true
  rw [hu]
  show (Option.bind (ψ.src? c) _).isSome = true
  rw [hv]
  rfl

/-- Parsing implication requires only successful parsing of its operands. -/
theorem source_parser_imp {C : Contract} {φ ψ : LFml C} {c : Bool}
    (hφ : (φ.src? c).isSome = true) (hψ : (ψ.src? c).isSome = true) :
    ((LFml.imp φ ψ).src? c).isSome = true := by
  obtain ⟨⟨u⟩, hu⟩ := Option.isSome_iff_exists.mp hφ
  obtain ⟨⟨v⟩, hv⟩ := Option.isSome_iff_exists.mp hψ
  show (Option.bind (φ.src? c) _).isSome = true
  rw [hu]
  show (Option.bind (ψ.src? c) _).isSome = true
  rw [hv]
  rfl

/-- Parsing negation preserves successful parsing. -/
theorem source_parser_not {C : Contract} {φ : LFml C} {c : Bool}
    (hφ : (φ.src? c).isSome = true) : ((LFml.not φ).src? c).isSome = true := by
  obtain ⟨⟨u⟩, hu⟩ := Option.isSome_iff_exists.mp hφ
  show ((φ.src? c).map _).isSome = true
  rw [hu]
  rfl

/-- Optional equality of numeric uint terms passes the actual parser at either flag. -/
theorem numeric_uint_optEq_parser {C : Contract} {P : Parameter → Prop} {E : EnvKey → Prop}
    {x y : LTm C (.val .uint)} (hx : x.Num P E) (hy : y.Num P E) (c : Bool) :
    ((LFml.optEq x y).src? c).isSome = true := by
  unfold LFml.optEq
  exact source_parser_and
    (source_parser_imp (numeric_uint_eq_parser hx hx c)
      (source_parser_imp (numeric_uint_eq_parser hy hy c) (numeric_uint_eq_parser hx hy c)))
    (source_parser_and
      (source_parser_imp (numeric_uint_eq_parser hx hx c) (numeric_uint_eq_parser hy hy c))
      (source_parser_imp (numeric_uint_eq_parser hy hy c) (numeric_uint_eq_parser hx hx c)))

/-- Numeric strict equality is unchanged by cutting, at every starting counter. -/
theorem numeric_eq_cut {C : Contract} {P : Parameter → Prop} {E : EnvKey → Prop}
    {p : PrimTy} {x y : LTm C (.val p)} (hx : x.Num P E) (hy : y.Num P E)
    (prev : List (LFml C)) (start : Nat) :
    (LFml.eq x y).cut prev start = ⟨.eq x y, [], start⟩ := by
  simp only [LFml.cut, numeric_cut_identity hx, numeric_cut_identity hy, List.append_nil]

/-- Numeric optional equality is unchanged by cutting, including its definedness tests. -/
theorem numeric_optEq_cut {C : Contract} {P : Parameter → Prop} {E : EnvKey → Prop}
    {p : PrimTy} {x y : LTm C (.val p)} (hx : x.Num P E) (hy : y.Num P E)
    (prev : List (LFml C)) (start : Nat) :
    (LFml.optEq x y).cut prev start = ⟨LFml.optEq x y, [], start⟩ := by
  simp only [LFml.optEq, LFml.cut, numeric_cut_identity hx, numeric_cut_identity hy,
    List.append_nil]

/-- Preparation chooses the original strict or optional equality of the prepared operands. -/
theorem uintEq_prepared_shape {C : Contract} {Γ : Ctx}
    {a b : Tm C Γ (.val .uint)} (ha : a.UIntLinear) (hb : b.UIntLinear)
    (x y : LTm C (.val .uint)) :
    (Fml.eqAt true a b x y).elim.condSimp.prenex =
      if a.totB || b.totB then .eq x.elim.condSimp y.elim.condSimp
      else LFml.optEq x.elim.condSimp y.elim.condSimp := by
  unfold Fml.eqAt
  rw [uintLinear_agrees ha, uintLinear_agrees hb]
  simp only [Bool.true_and, if_true]
  split <;> rfl

/-- The actual prepared uint equality passes the parser, needs no cut and has no conditionals. -/
theorem uintEq_prepared_invariants {C : Contract} {Γ : Ctx}
    {a b : Tm C Γ (.val .uint)} (ha : a.UIntLinear) (hb : b.UIntLinear)
    {P : Parameter → Prop} {E : EnvKey → Prop} {x y : LTm C (.val .uint)}
    (hx : x.Num P E) (hy : y.Num P E) :
    let ψ := (Fml.eqAt true a b x y).elim.condSimp.prenex
    (∀ c : Bool, (ψ.src? c).isSome = true) ∧
      (∀ prev start, ψ.cut prev start = ⟨ψ, [], start⟩) ∧ ψ.conds = 0 := by
  let Q (ψ : LFml C) : Prop :=
    (∀ c : Bool, (ψ.src? c).isSome = true) ∧
      (∀ prev start, ψ.cut prev start = ⟨ψ, [], start⟩) ∧ ψ.conds = 0
  change Q _
  apply (congrArg Q (uintEq_prepared_shape ha hb x y)).mpr
  have hNx : x.elim.condSimp.Num P E := numeric_prepared hx
  have hNy : y.elim.condSimp.Num P E := numeric_prepared hy
  have hCx : x.elim.condSimp.conds = 0 := numeric_no_conds hNx
  have hCy : y.elim.condSimp.conds = 0 := numeric_no_conds hNy
  by_cases ht : (a.totB || b.totB) = true
  · rw [if_pos ht]
    dsimp only [Q]
    exact ⟨numeric_uint_eq_parser hNx hNy, numeric_eq_cut hNx hNy,
      by simp only [LFml.conds, hCx, hCy, Nat.zero_add]⟩
  · rw [if_neg ht]
    dsimp only [Q]
    exact ⟨numeric_uint_optEq_parser hNx hNy, numeric_optEq_cut hNx hNy,
      by simp only [LFml.optEq, LFml.conds, hCx, hCy, Nat.zero_add]⟩

/-- Actual source reduction, with parser, cut and conditional invariants in addition to the source bound. -/
theorem uintPrefix_prepared_coverageFacts {C : Contract} (name : Var)
    {a b : Tm C [.val .uint] (.val .uint)} (ha : a.UIntLinear) (hb : b.UIntLinear) :
    ∃ ψ : LFml C, leafOf? (primitivePrefixEq name a b) = some (.all 0 .uint ψ) ∧
      (∀ c : Bool, ψ.Src c true) ∧ (∀ q ∈ ψ.parameters, q = ⟨.uint, 0⟩) ∧
      ψ.condMax = 2 ∧ ψ.nodes ≤ 7 * (a.size + b.size) + 13 ∧
      (∀ c : Bool, (ψ.src? c).isSome = true) ∧
      (∀ prev start, ψ.cut prev start = ⟨ψ, [], start⟩) ∧ ψ.conds = 0 := by
  obtain ⟨x, hx, hNx, hEx, hCx, hSx⟩ := uintLinear_prefix_sourceBound ha
  obtain ⟨y, hy, hNy, hEy, hCy, hSy⟩ := uintLinear_prefix_sourceBound hb
  rw [toLT_eq_toL_of_agree a _ (uintLinear_agrees ha)] at hx
  rw [toLT_eq_toL_of_agree b _ (uintLinear_agrees hb)] at hy
  let θ : LFml C := Fml.eqAt true a b x y
  have hp : (Fml.eq a b).toLS true ((SymS.init (C := C)).pushQ .uint) = some θ := by
    change (a.toL ((SymS.init (C := C)).pushQ .uint)).bind
      (fun u => (b.toL ((SymS.init (C := C)).pushQ .uint)).map
        (fun v => Fml.eqAt true a b u v)) = some θ
    rw [hx, hy]
    rfl
  have hn : (Fml.eq a b).toLS false ((SymS.init (C := C)).pushQ .uint) = some θ := by
    change (a.toL ((SymS.init (C := C)).pushQ .uint)).bind
      (fun u => (b.toL ((SymS.init (C := C)).pushQ .uint)).map
        (fun v => Fml.eqAt false a b u v)) = some θ
    rw [hx, hy]
    exact congrArg some (uintLinear_eqAt_polarity ha hb x y false)
  have hs : (sourceReduction? (primitivePrefixEq name a b)).map (·.leaf) =
      some (.all 0 .uint θ) := uintPrefix_source_from_polarities name θ hp hn
  refine ⟨θ.elim.condSimp.prenex, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact leafOf_of_normalized_source (primitivePrefixEq name a b) (.all 0 .uint θ)
      (primitivePrefixEq_normalizes name a b) hs
  · intro c
    exact uintEq_prepared_source ha hb hNx hNy c true
  · exact uintEq_prepared_parameters ha hb hNx hNy
  · exact uintEq_prepared_condMax ha hb hNx hNy
  · have hn : θ.elim.condSimp.prenex.nodes ≤ 7 * x.nodes + 7 * y.nodes + 13 :=
      uintEq_prepared_nodes_le ha hb hEx hEy hCx hCy
    omega

  · exact uintEq_prepared_invariants ha hb hNx hNy

/-- A numeric prefix body's actual parser, no-cut and size facts discharge the unchanged exact tests. -/
theorem numeric_prefix_exact_tests {C : Contract} {ψ : LFml C}
    (hsrc : ψ.Src false true) (hp : ∀ q ∈ ψ.parameters, q = ⟨.uint, 0⟩)
    (hc : ψ.condMax = 2) (hn : ψ.nodes ≤ 511)
    (hparse : (ψ.src? true).isSome = true)
    (hcut : ∀ prev start, ψ.cut prev start = ⟨ψ, [], start⟩) (hzero : ψ.conds = 0) :
    (LFml.all 0 .uint ψ).inExact = true ∧ (LFml.all 0 .uint ψ).exactBounded = true := by
  have hshape : ψ.allDepth = 0 ∧ ψ.stripAll = ([], ψ) := source_body_shape hsrc
  have hbody : ψ.stripAll.2 = ψ := congrArg Prod.snd hshape.2
  have hparseStrip : (ψ.stripAll.2.src? true).isSome = true :=
    (congrArg (fun φ : LFml C => (φ.src? true).isSome) hbody).trans hparse
  have hparams : ψ.parameters.all (fun q => decide (q ∈ [⟨.uint, 0⟩])) = true := by
    apply List.all_eq_true.mpr
    intro q hq
    simp only [decide_eq_true_eq]
    exact List.mem_singleton.mpr (hp q hq)
  have hallzero : (LFml.all 0 .uint ψ).conds = 0 := hzero
  have hlift : (LFml.all 0 .uint ψ).liftCond condLiftFuel = .all 0 .uint ψ := by
    simpa only [LFml.condSimp_of_conds _ hallzero] using
      LFml.liftCond_condSimp_of_conds condLiftFuel (.all 0 .uint ψ) hallzero
  have hcutall : ψ.cutAll = ψ := by
    simp only [LFml.cutAll, hcut]
  constructor
  · simp only [LFml.inExact, LFml.allDepth, LFml.stripAll, hshape.1, hshape.2,
      hparseStrip, hparams, hc] <;> rfl
  · simp only [LFml.exactBounded, hlift, LFml.stripAll, hshape.2, hcutall]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hn, hn⟩

/-- A sufficient source-sized class passes the existing exact coverage route.
The raw size premise is sufficient only; larger sources and uncovered inputs may still be decided. -/
theorem uintPrefix_Covered {C : Contract} (name : Var)
    {a b : Tm C [.val .uint] (.val .uint)} (ha : a.UIntLinear) (hb : b.UIntLinear)
    (hs : a.size + b.size ≤ 71) : (primitivePrefixEq name a b).Covered = true := by
  obtain ⟨ψ, hl, hsrc, hp, hc, hn, hparse, hcut, hzero⟩ :=
    uintPrefix_prepared_coverageFacts name ha hb
  have hn511 : ψ.nodes ≤ 511 := by omega
  obtain ⟨hi, hbnd⟩ := numeric_prefix_exact_tests (hsrc false) hp hc hn511 (hparse true) hcut hzero
  have hin : (primitivePrefixEq name a b).inExact = true := by
    simpa only [Fml.inExact, hl] using hi
  have hbound : (primitivePrefixEq name a b).exactBounded = true := by
    simpa only [Fml.exactBounded, hl] using hbnd
  simp only [Fml.Covered, Fml.CoveredA, hin, hbound, Bool.true_and, Bool.true_or]

/-- This explicit source family is decided with the unchanged hash-free premise discharged. -/
theorem uintPrefix_decided {C : Contract} (name : Var)
    {a b : Tm C [.val .uint] (.val .uint)} (ha : a.UIntLinear) (hb : b.UIntLinear)
    (hs : a.size + b.size ≤ 71) : decideGoal (primitivePrefixEq name a b) ≠ .unknown :=
  decideGoal_complete (uintPrefix_Covered name ha hb hs) (uintPrefix_hashFree name ha hb)

/-- Every answer on this explicit source class carries the existing kernel certificate. -/
theorem uintPrefix_certified {C : Contract} (name : Var)
    {a b : Tm C [.val .uint] (.val .uint)} (ha : a.UIntLinear) (hb : b.UIntLinear)
    (hs : a.size + b.size ≤ 71) :
    (decideGoal (primitivePrefixEq name a b) = .proved ∧ Fml.ValidH (primitivePrefixEq name a b)) ∨
      ∃ σ : State C [], decideGoal (primitivePrefixEq name a b) = .refuted σ ∧
        ¬ Fml.holdsH σ (primitivePrefixEq name a b) := by
  have hd : decideGoal (primitivePrefixEq name a b) ≠ .unknown := uintPrefix_decided name ha hb hs
  cases hv : decideGoal (primitivePrefixEq name a b) with
  | proved => exact Or.inl ⟨rfl, decideGoal_sound hv⟩
  | refuted σ => exact Or.inr ⟨σ, rfl, decideGoal_refutes hv⟩
  | unknown => exact False.elim (hd hv)

end Solidity.Decide
