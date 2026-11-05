import Solidity.Calculus.DecisionLeafPreparation

/-!
# Numeric formula preparation facts

These connect actual numeric source outputs to formula source/parameter facts.
Coverage, formula-size bounds and the exhaustive target bridge remain separate.
-/
namespace Solidity.Decide

/-- Actual parameter enumeration respects the existing numeric grammar predicate. -/
theorem numeric_parameters {C : Contract} {P : Parameter → Prop} {E : EnvKey → Prop}
    {p : PrimTy} {t : LTm C (.val p)} (h : t.Num P E) :
    ∀ q ∈ t.parameters, P q := by
  induction h with
  | var k hk => simpa only [LTm.parameters, List.mem_singleton, forall_eq] using hk
  | lit v => intro q hq; cases hq
  | env e he => intro q hq; cases hq
  | err => intro q hq; cases hq
  | neg h ha iha => exact iha
  | bnot h ha iha => exact iha
  | add h ha hb iha ihb | sub h ha hb iha ihb | seq ha hb iha ihb =>
    intro q hq
    rcases List.mem_append.mp hq with hqa | hqb
    · exact iha q hqa
    · exact ihb q hqb
  | mulL h v ha iha =>
    simpa only [LTm.parameters, List.nil_append] using iha
  | mulR h v ha iha =>
    simpa only [LTm.parameters, List.append_nil] using iha

/-- Numeric optional equality remains in the source grammar after actual preparation. -/
theorem uintEq_prepared_source {C : Contract} {Γ : Ctx}
    {a b : Tm C Γ (.val .uint)} (ha : a.UIntLinear) (hb : b.UIntLinear)
    {P : Parameter → Prop} {E : EnvKey → Prop} {x y : LTm C (.val .uint)}
    (hx : x.Num P E) (hy : y.Num P E) (c w : Bool) :
    (Fml.eqAt true a b x y).elim.condSimp.prenex.Src c w := by
  have hsx : (x.elim : LTm C (.val .uint)).condSimp.Src c w .num :=
    numeric_source (numeric_prepared hx) c w
  have hsy : (y.elim : LTm C (.val .uint)).condSimp.Src c w .num :=
    numeric_source (numeric_prepared hy) c w
  unfold Fml.eqAt
  rw [uintLinear_agrees ha, uintLinear_agrees hb]
  simp only [Bool.true_and, if_true]
  split
  · exact LFml.SrcL.ofNums hsx hsy
  · exact optEq_numeric_src hsx hsy

/-- Optional equality introduces no parameter outside its two operands. -/
theorem optEq_parameters {C : Contract} {P : Parameter → Prop} {p : PrimTy}
    {x y : LTm C (.val p)} (hx : ∀ q ∈ x.parameters, P q) (hy : ∀ q ∈ y.parameters, P q) :
    ∀ q ∈ (LFml.optEq x y).parameters, P q := by
  simp only [LFml.optEq, LFml.parameters, List.forall_mem_append]
  exact ⟨⟨⟨hx, hx⟩, ⟨⟨hy, hy⟩, ⟨hx, hy⟩⟩⟩, ⟨⟨⟨hx, hx⟩, ⟨hy, hy⟩⟩, ⟨⟨hy, hy⟩, ⟨hx, hx⟩⟩⟩⟩

/-- Prepared optional/strict source equality enumerates only permitted numeric atoms. -/
theorem uintEq_prepared_parameters {C : Contract} {Γ : Ctx}
    {a b : Tm C Γ (.val .uint)} (ha : a.UIntLinear) (hb : b.UIntLinear)
    {P : Parameter → Prop} {E : EnvKey → Prop} {x y : LTm C (.val .uint)}
    (hx : x.Num P E) (hy : y.Num P E) :
    ∀ q ∈ (Fml.eqAt true a b x y).elim.condSimp.prenex.parameters, P q := by
  have hpx : ∀ q ∈ (x.elim : LTm C (.val .uint)).condSimp.parameters, P q :=
    numeric_parameters (numeric_prepared hx)
  have hpy : ∀ q ∈ (y.elim : LTm C (.val .uint)).condSimp.parameters, P q :=
    numeric_parameters (numeric_prepared hy)
  unfold Fml.eqAt
  rw [uintLinear_agrees ha, uintLinear_agrees hb]
  simp only [Bool.true_and, if_true]
  split
  · exact List.forall_mem_append.mpr ⟨hpx, hpy⟩
  · exact optEq_parameters hpx hpy

/-- No conditional splitting is needed in either prepared numeric equality branch. -/
theorem uintEq_prepared_condMax {C : Contract} {Γ : Ctx}
    {a b : Tm C Γ (.val .uint)} (ha : a.UIntLinear) (hb : b.UIntLinear)
    {P : Parameter → Prop} {E : EnvKey → Prop} {x y : LTm C (.val .uint)}
    (hx : x.Num P E) (hy : y.Num P E) :
    (Fml.eqAt true a b x y).elim.condSimp.prenex.condMax = 2 := by
  have hcx : (x.elim : LTm C (.val .uint)).condSimp.conds = 0 :=
    numeric_no_conds (numeric_prepared hx)
  have hcy : (y.elim : LTm C (.val .uint)).condSimp.conds = 0 :=
    numeric_no_conds (numeric_prepared hy)
  unfold Fml.eqAt
  rw [uintLinear_agrees ha, uintLinear_agrees hb]
  simp only [Bool.true_and, if_true]
  split <;> simp only [LFml.elim, LFml.condSimp, LFml.prenex, LFml.optEq, LFml.condMax, hcx, hcy] <;> rfl

/-- Actual body translations compose through the unchanged positive uint prefix reducer. -/
theorem uintPrefix_source_from_polarities {C : Contract} (x : Var)
    {a b : Tm C [.val .uint] (.val .uint)} (ψ : LFml C)
    (hp : (Fml.eq a b).toLS true ((SymS.init (C := C)).pushQ .uint) = some ψ)
    (hn : (Fml.eq a b).toLS false ((SymS.init (C := C)).pushQ .uint) = some ψ) :
    (sourceReduction? (primitivePrefixEq x a b)).map (·.leaf) = some (.all 0 .uint ψ) := by
  have hd : (ExactAt.directional? ((SymS.init (C := C)).pushQ .uint) (.eq a b)).map (·.leaf) = some ψ :=
    directional_leaf_of_polarities ((SymS.init (C := C)).pushQ .uint) (.eq a b) ψ hp hn
  cases hr : ExactAt.directional? ((SymS.init (C := C)).pushQ .uint) (.eq a b) with
  | none => rw [hr] at hd; cases hd
  | some r =>
    rw [hr] at hd
    have hl : r.leaf = ψ := Option.some.inj hd
    simp only [primitivePrefixEq, sourceReduction?, ExactAt.ofFormula?, Option.bind_eq_bind, Option.pure_def, hr,
      Option.orElse_some, Option.map_some, Option.bind_some, ExactAt.all]
    exact congrArg (fun B : LFml C => some (LFml.all 0 .uint B)) hl

/-- Source bodies have no universal prefix of their own. -/
theorem source_body_shape {C : Contract} {c w : Bool} {φ : LFml C} (h : φ.Src c w) :
    φ.allDepth = 0 ∧ φ.stripAll = ([], φ) := by
  cases h <;> exact ⟨rfl, rfl⟩

/-- Construct the actual prepared prefix body and its source/atom/lifting-weight facts. -/
theorem uintPrefix_prepared_facts {C : Contract} (name : Var)
    {a b : Tm C [.val .uint] (.val .uint)} (ha : a.UIntLinear) (hb : b.UIntLinear) :
    ∃ ψ : LFml C, leafOf? (primitivePrefixEq name a b) = some (.all 0 .uint ψ) ∧
      (∀ c : Bool, ψ.Src c true) ∧
      (∀ q ∈ ψ.parameters, q = ⟨.uint, 0⟩) ∧ ψ.condMax = 2 := by
  obtain ⟨x, hx, hNx⟩ := uintLinear_prefix_numeric ha
  obtain ⟨y, hy, hNy⟩ := uintLinear_prefix_numeric hb
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
  refine ⟨θ.elim.condSimp.prenex, ?_, ?_, ?_, ?_⟩
  · exact leafOf_of_normalized_source (primitivePrefixEq name a b) (.all 0 .uint θ)
      (primitivePrefixEq_normalizes name a b) hs
  · intro c
    exact uintEq_prepared_source ha hb hNx hNy c true
  · exact uintEq_prepared_parameters ha hb hNx hNy
  · exact uintEq_prepared_condMax ha hb hNx hNy

/-- The actual prepared numeric prefix already satisfies the existing lifted fragment check.
This does not assert the separate cut/node bounds or complete coverage. -/
theorem uintPrefix_prepared_liftedExact {C : Contract} (name : Var)
    {a b : Tm C [.val .uint] (.val .uint)} (ha : a.UIntLinear) (hb : b.UIntLinear) :
    ∃ ψ : LFml C, leafOf? (primitivePrefixEq name a b) = some ψ ∧ ψ.liftedExact = true := by
  obtain ⟨β, hl, hs, hp, hc⟩ := uintPrefix_prepared_facts name ha hb
  have hshape : β.allDepth = 0 ∧ β.stripAll = ([], β) := source_body_shape (hs false)
  have hsrc : (β.src? false).isSome = true := LFml.src?_complete (hs false)
  have hbody : β.stripAll.2 = β := congrArg Prod.snd hshape.2
  have hsrcStrip : (β.stripAll.2.src? false).isSome = true :=
    (congrArg (fun φ : LFml C => (φ.src? false).isSome) hbody).trans hsrc
  have hparams : β.parameters.all (fun q => decide (q ∈ [⟨.uint, 0⟩])) = true := by
    apply List.all_eq_true.mpr
    intro q hq
    simp only [decide_eq_true_eq]
    exact List.mem_singleton.mpr (hp q hq)
  refine ⟨.all 0 .uint β, hl, ?_⟩
  simp only [LFml.liftedExact, LFml.allDepth, LFml.stripAll, hshape.1, hshape.2, hsrcStrip, hparams] <;> rfl

/-- Every member of the supported source family is hash-free. -/
theorem uintPrefix_hashFree {C : Contract} (name : Var)
    {a b : Tm C [.val .uint] (.val .uint)} (ha : a.UIntLinear) (hb : b.UIntLinear) :
    (primitivePrefixEq name a b).hasHash = false := by
  simp only [primitivePrefixEq, Fml.hasHash, uintLinear_hashFree ha,
    uintLinear_hashFree hb, Bool.false_or]

/-- Admission of this supported source family by the entire unchanged predicate, for every waiver setting. -/
theorem uintPrefix_inTarget {C : Contract} (name : Var)
    {a b : Tm C [.val .uint] (.val .uint)} (ha : a.UIntLinear) (hb : b.UIntLinear) (w : Waivers) :
    (primitivePrefixEq name a b).inTarget w = true := by
  have he : (primitivePrefixEq name a b).target w true false =
      (Fml.eq a b).target w true false := by
    cases hr : (Fml.eq a b).readsAt [0] <;>
      simp only [primitivePrefixEq, Fml.target, List.length_nil, hr] <;> rfl
  have ht : (primitivePrefixEq name a b).target w true false = true :=
    he.trans (qfUIntLinear_target (.eq ha hb) w true false)
  unfold Fml.inTarget
  rw [ht]
  simp only [primitivePrefixEq, Fml.mapKeys, Fml.negPairUnread,
    uintLinear_mapKeys ha, uintLinear_mapKeys hb, List.nil_append,
    Bool.not_true, Bool.false_and, Bool.false_or]
  rfl

end Solidity.Decide
