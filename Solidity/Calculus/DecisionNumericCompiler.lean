import Solidity.Calculus.DecisionNumericStages

/-! # Numeric compilation from equation-operand depth
This consumes the existing arithmetic compiler at unchanged fuel1024. The
aggregate511-node admission test and global decision behavior are unchanged.
-/
namespace Solidity.Decide

/-- Maximum existing term depth at an equation, independent of logical size. -/
def LFml.equationDepth : LFml C → Nat
  | .tt => 0
  | .eq a b => max a.depth b.depth
  | .not φ | .all _ _ φ => φ.equationDepth
  | .and φ ψ | .imp φ ψ => max φ.equationDepth ψ.equationDepth

theorem LFml.equationDepth_le_depth {C : Contract} (φ : LFml C) :
    φ.equationDepth ≤ φ.depth := by
  induction φ with
  | tt => simp only [LFml.equationDepth, LFml.depth]; omega
  | eq a b => simp only [LFml.equationDepth, LFml.depth]; omega
  | not φ ih | all k p φ ih => simp only [LFml.equationDepth, LFml.depth]; omega
  | and φ ψ ihφ ihψ | imp φ ψ ihφ ihψ =>
    simp only [LFml.equationDepth, LFml.depth]
    omega

theorem numeric_mono {C : Contract} {P P' : Parameter → Prop} {E E' : EnvKey → Prop}
    {p : PrimTy} {t : LTm C (.val p)} (h : t.Num P E)
    (hP : ∀ q, P q → P' q) (hE : ∀ e, E e → E' e) : t.Num P' E' := by
  induction h with
  | var k hk => exact .var k (hP _ hk)
  | lit v => exact .lit v
  | env e he => exact .env e (hE _ he)
  | add hop ha hb iha ihb => exact .add hop iha ihb
  | sub hop ha hb iha ihb => exact .sub hop iha ihb
  | mulL hop v hb ihb => exact .mulL hop v ihb
  | mulR hop v ha iha => exact .mulR hop v iha
  | neg hop ha iha => exact .neg hop iha
  | bnot hop ha iha => exact .bnot hop iha
  | seq ha hb iha ihb => exact .seq iha ihb
  | err => exact .err

theorem LFml.UIntQF.mono {C : Contract} {P P' : Parameter → Prop} {E E' : EnvKey → Prop}
    {φ : LFml C} (h : φ.UIntQF P E)
    (hP : ∀ q, P q → P' q) (hE : ∀ e, E e → E' e) : φ.UIntQF P' E' := by
  induction h with
  | tt => exact .tt
  | eq ha hb => exact .eq (numeric_mono ha hP hE) (numeric_mono hb hP hE)
  | not ha ih => exact .not ih
  | and ha hb iha ihb => exact .and iha ihb
  | imp ha hb iha ihb => exact .imp iha ihb

/-- This grammar reaches the unchanged compiler fragment by operand depth;
no total formula-node limit is used in this stage. -/
theorem LFml.UIntQF.arith_equationDepth {C : Contract} {P : Parameter → Prop} {E : EnvKey → Prop}
    {φ : LFml C} (h : φ.UIntQF P E) :
    φ.equationDepth ≤ 1023 → φ.Arith P E := by
  induction h with
  | tt => intro hd; exact .tt
  | eq ha hb =>
    intro hd
    simp only [LFml.equationDepth] at hd
    exact .eqN rfl ha hb (by omega) (by omega)
  | not ha ih => intro hd; exact .not (ih hd)
  | and ha hb iha ihb =>
    intro hd
    simp only [LFml.equationDepth] at hd
    exact .and (iha (by omega)) (ihb (by omega))
  | imp ha hb iha ihb =>
    intro hd
    simp only [LFml.equationDepth] at hd
    exact .imp (iha (by omega)) (ihb (by omega))

/-- Uses the actual collected parameter/environment lists and real compiler. -/
theorem numeric_leafArithmetic_of_equationDepth {C : Contract}
    {P : Parameter → Prop} {E : EnvKey → Prop} {φ : LFml C}
    (h : φ.UIntQF P E) (hd : φ.equationDepth ≤ 1023) :
    (leafArithmetic? φ).isSome = true := by
  have hg : φ.UIntQF (fun _ => True) (fun _ => True) := h.mono (fun _ _ => trivial) (fun _ _ => trivial)
  have ha : φ.Arith (fun _ => True) (fun _ => True) := hg.arith_equationDepth hd
  exact leafArithmetic?_isSome φ (ha.restrict
    (fun q hq => (List.mem_eraseDups' _ q).mpr hq)
    (fun e he => ((Inputs.unique_spec _).2 e).mpr he))

/-- The real returned certificate preserves validity over actual states/atoms. -/
theorem numeric_leafArithmetic_certificate {C : Contract}
    {P : Parameter → Prop} {E : EnvKey → Prop} {φ : LFml C}
    (h : φ.UIntQF P E) (hd : φ.equationDepth ≤ 1023) :
    ∃ r : LeafArithmetic φ, leafArithmetic? φ = some r ∧ (φ.Valid ↔ r.arithmetic.Valid) := by
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp (numeric_leafArithmetic_of_equationDepth h hd)
  exact ⟨r, hr, r.valid_iff⟩

/-- Read-free numeric flattening reaches the actual checked read-layout
wrapper with a formula-derived node budget; zero reads need no alias budget. -/
theorem numeric_readFlatten_resources {C : Contract}
    {P : Parameter → Prop} {E : EnvKey → Prop} {φ : LFml C}
    (h : φ.UIntQF P E) (hd : φ.equationDepth ≤ 1023)
    (budget : Nat) (hn : φ.nodes ≤ budget) :
    ∃ r : ReadFlattening φ φ.atomBound, readFlatten? budget φ = some r ∧
      r.flat.reads = [] ∧ r.formula = .imp .tt φ := by
  have hg : φ.UIntQF (fun _ => True) (fun _ => True) := h.mono (fun _ _ => trivial) (fun _ _ => trivial)
  have harith : φ.Arith (fun _ => True) (fun _ => True) := hg.arith_equationDepth hd
  obtain ⟨a, ha, haf, har⟩ := numeric_formula_flattenFuel h budget budget φ.atomBound
    (Nat.le_trans (LFml.depth_le_nodes φ) hn) hn
  have hflat : flattenFormula? budget φ = some a := by
    simp only [flattenFormula?, flattenFormulaAt?, ha, Option.map_some]
  obtain ⟨src, hsrc, hz⟩ := harith.readFree
  have hfree : (readFreeFormula? a.formula).isSome = true := by
    rw [haf]
    simp only [readFreeFormula?, hsrc, Option.bind_eq_bind, Option.bind_some, hz, dif_pos, Option.pure_def, Option.isSome_some]
  obtain ⟨free, hfree⟩ := Option.isSome_iff_exists.mp hfree
  have hlaid : Laid a.reads φ.atomBound := by rw [har]; exact .nil _
  obtain ⟨layout, hlayout⟩ := Option.isSome_iff_exists.mp
    (occurrenceLayout?_isSome budget hlaid (by rw [har]; simp only [List.length_nil]; omega))
  let r : ReadFlattening φ φ.atomBound := ⟨a, src, Nat.le_refl _, layout, free⟩
  have hr : readFlatten? budget φ = some r := by
    simp only [readFlatten?, hflat, hsrc, hlayout, hfree, Option.bind_eq_bind, Option.bind_some]
    rfl
  refine ⟨r, hr, har, ?_⟩
  change (.imp (ReadOccurrence.constraints a.reads) a.formula : LFml C) = _
  rw [har, haf]
  rfl

/-- The actual existing cut/read-layout/compiler producer succeeds for this
read-free class under structural nodes and unchanged operand-depth limits. -/
theorem numeric_flattenedArithmetic_resources {C : Contract}
    {P : Parameter → Prop} {E : EnvKey → Prop} {φ : LFml C}
    (h : φ.UIntQF P E) (hd : φ.equationDepth ≤ 1023)
    (budget : Nat) (hn : φ.nodes ≤ budget) :
    (flattenedArithmetic? budget φ).isSome = true := by
  have hcut : φ.cutAll = φ := by simp only [LFml.cutAll, h.cut_identity]
  have hgc : φ.cutAll.UIntQF P E := by rw [hcut]; exact h
  have hdc : φ.cutAll.equationDepth ≤ 1023 := by rw [hcut]; exact hd
  have hnc : φ.cutAll.nodes ≤ budget := by rw [hcut]; exact hn
  obtain ⟨r, hr, hreads, hformula⟩ := numeric_readFlatten_resources hgc hdc budget hnc
  have hg : φ.cutAll.UIntQF (fun _ => True) (fun _ => True) := hgc.mono (fun _ _ => trivial) (fun _ _ => trivial)
  have harith : r.formula.Arith (fun _ => True) (fun _ => True) := by
    rw [hformula]
    exact .imp .tt (hg.arith_equationDepth hdc)
  have hencode : (leafArithmetic? r.formula).isSome = true :=
    leafArithmetic?_isSome _ (harith.restrict
      (fun q hq => (List.mem_eraseDups' _ q).mpr hq)
      (fun e he => ((Inputs.unique_spec _).2 e).mpr he))
  obtain ⟨encoding, hencoding⟩ := Option.isSome_iff_exists.mp hencode
  obtain ⟨source, hsource⟩ := (h.source false false).readFormula
  simp only [flattenedArithmetic?, hsource, hr, Option.bind_eq_bind, Option.bind_some,
    hreads, List.length_nil, Nat.zero_mul, Nat.zero_le, if_pos, hencoding, Option.pure_def,
    Option.isSome_some]

theorem numeric_flattenedArithmetic_certificate {C : Contract}
    {P : Parameter → Prop} {E : EnvKey → Prop} {φ : LFml C}
    (h : φ.UIntQF P E) (hd : φ.equationDepth ≤ 1023)
    (budget : Nat) (hn : φ.nodes ≤ budget) :
    ∃ r : FlattenedArithmetic φ, flattenedArithmetic? budget φ = some r ∧
      (φ.Valid ↔ r.encoding.arithmetic.Valid) := by
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp (numeric_flattenedArithmetic_resources h hd budget hn)
  exact ⟨r, hr, r.valid_iff⟩

/-- Source syntax reaches its actual closed leaf and existing arithmetic
compiler. The source-weight bound is sufficient, not a changed runtime cap. -/
theorem qfUIntGround_compiler_stage {C : Contract} {φ : Fml C []}
    (h : φ.QFUIntLinear) (hw : φ.uintQFWeight ≤ 1023) :
    ∃ ψ : LFml C, leafOf? φ = some ψ ∧
      ψ.UIntQF (fun _ => False) (fun _ => False) ∧ ψ.nodes ≤ φ.uintQFWeight ∧
      ∃ r : LeafArithmetic ψ, leafArithmetic? ψ = some r ∧ (ψ.Valid ↔ r.arithmetic.Valid) := by
  obtain ⟨ψ, hl, hg, hn⟩ := qfUIntGround_leaf_stage h (by omega)
  have hd : ψ.equationDepth ≤ 1023 :=
    Nat.le_trans (ψ.equationDepth_le_depth)
      (Nat.le_trans (LFml.depth_le_nodes ψ) (Nat.le_trans hn hw))
  obtain ⟨r, hr, hc⟩ := numeric_leafArithmetic_certificate hg hd
  exact ⟨ψ, hl, hg, hn, r, hr, hc⟩

/-- Positive-prefix source discovery is composed concretely; the prefix is
retained, and this certificate compiles its actual numeric body only. -/
theorem qfUIntPrefix_compiler_stage {C : Contract} (name : Var)
    {φ : Fml C [.val .uint]} (h : φ.QFUIntLinear) (hw : φ.uintQFWeight ≤ 1023) :
    ∃ ψ : LFml C, leafOf? (.all name .uint φ) = some (.all 0 .uint ψ) ∧
      ψ.UIntQF (fun q => q = ⟨.uint, 0⟩) (fun _ => False) ∧ ψ.nodes ≤ φ.uintQFWeight ∧
      ∃ r : LeafArithmetic ψ, leafArithmetic? ψ = some r ∧ (ψ.Valid ↔ r.arithmetic.Valid) := by
  obtain ⟨ψ, hl, hg, hn⟩ := qfUIntPrefix_leaf_stage name h (by omega)
  have hd : ψ.equationDepth ≤ 1023 :=
    Nat.le_trans (ψ.equationDepth_le_depth)
      (Nat.le_trans (LFml.depth_le_nodes ψ) (Nat.le_trans hn hw))
  obtain ⟨r, hr, hc⟩ := numeric_leafArithmetic_certificate hg hd
  exact ⟨ψ, hl, hg, hn, r, hr, hc⟩

/-- Actual closed-source leaf followed by the existing full numeric producer,
with its traversal budget derived from that leaf's structural nodes. -/
theorem qfUIntGround_flattenedArithmetic_stage {C : Contract} {φ : Fml C []}
    (h : φ.QFUIntLinear) (hw : φ.uintQFWeight ≤ 1023) :
    ∃ ψ : LFml C, leafOf? φ = some ψ ∧ ψ.nodes ≤ φ.uintQFWeight ∧
      ∃ r : FlattenedArithmetic ψ, flattenedArithmetic? ψ.nodes ψ = some r ∧
        (ψ.Valid ↔ r.encoding.arithmetic.Valid) := by
  obtain ⟨ψ, hl, hg, hn, enc, he, hc⟩ := qfUIntGround_compiler_stage h hw
  have hd : ψ.equationDepth ≤ 1023 := Nat.le_trans ψ.equationDepth_le_depth
    (Nat.le_trans (LFml.depth_le_nodes ψ) (Nat.le_trans hn hw))
  obtain ⟨r, hr, hv⟩ := numeric_flattenedArithmetic_certificate hg hd ψ.nodes (Nat.le_refl _)
  exact ⟨ψ, hl, hn, r, hr, hv⟩

/-- The prefix stays present; only its actual numeric body is compiled. -/
theorem qfUIntPrefix_flattenedArithmetic_stage {C : Contract} (name : Var)
    {φ : Fml C [.val .uint]} (h : φ.QFUIntLinear) (hw : φ.uintQFWeight ≤ 1023) :
    ∃ ψ : LFml C, leafOf? (.all name .uint φ) = some (.all 0 .uint ψ) ∧
      ψ.nodes ≤ φ.uintQFWeight ∧
      ∃ r : FlattenedArithmetic ψ, flattenedArithmetic? ψ.nodes ψ = some r ∧
        (ψ.Valid ↔ r.encoding.arithmetic.Valid) := by
  obtain ⟨ψ, hl, hg, hn, enc, he, hc⟩ := qfUIntPrefix_compiler_stage name h hw
  have hd : ψ.equationDepth ≤ 1023 := Nat.le_trans ψ.equationDepth_le_depth
    (Nat.le_trans (LFml.depth_le_nodes ψ) (Nat.le_trans hn hw))
  obtain ⟨r, hr, hv⟩ := numeric_flattenedArithmetic_certificate hg hd ψ.nodes (Nat.le_refl _)
  exact ⟨ψ, hl, hn, r, hr, hv⟩

end Solidity.Decide
