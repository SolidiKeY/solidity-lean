import Solidity.Calculus.ArrayCut
import Solidity.Calculus.AutoComplete

/-!
# Leaves that read storage arrays (M7, step 6)

The automatic pipeline of `Calculus/DependentReduction.lean` on a leaf that
reads a storage array of primitives at a root at a symbolic index: updates
pushed in with the Theory's reads exact (`Calculus/TheoryRead.lean`), reads
of writes eliminated, the universal prefix stripped, then

* the fallbacks of the Theory's reads lifted (`LFml.orLift`,
  `Calculus/OrLift.lean`);
* the array reads cut to atoms, what actual arrays make of them in front
  (`LFml.aCut?`, `Calculus/ArrayCut.lean`);
* the guards extracted (`LFml.gx`), the conditionals lifted, and the rest
  flattened and decided as in M4 (`flattenedArithmetic?`).

Each stage is exact in a universal reading, so the verdict is exact
(`ArrayReduction.valid_iff`); a false assignment is realized as in M4, then
its arrays rebuilt from the atoms (`ARead.realize`), which refutes the leaf
(`LFml.aCut_refutes`).  `Fml.arrayCovered` is the fragment, on the
eliminated leaf; `arrayReduction?_isSome` proves the pipeline never refuses
it.
-/

namespace Solidity.Decide

open ReadRealization Linear

variable {C : Contract}

/-- The depth to which the Theory's fallbacks are lifted. -/
def orFuel : Nat := 16

/-- The most fallbacks lifted out of a body (each lift doubles its
equation). -/
def orBudget : Nat := 8

/-- **The array stages of a leaf's body**: its universal prefix, the
fallbacks lifted and the arrays cut. -/
structure ArrayBody (ψ : LFml C) where
  pre : UniversalPrefix ψ
  covered : ∀ p ∈ pre.body.parameters, p ∈ pre.parameters
  cut : LFml C
  reads : List (ARead C)
  hcut : (pre.body.orLift orFuel).aCut? (pre.body.orLift orFuel).atomBound = some (cut, reads)

namespace ArrayBody

/-- The leaf the arithmetic stages take. -/
abbrev leaf {ψ : LFml C} (b : ArrayBody ψ) : LFml C := b.cut.gx.liftCond condLiftFuel

theorem holds_body {ψ : LFml C} (b : ArrayBody ψ) (g : State C []) (ν : AEnv)
    (h : ψ.holds g AEnv.dflt) : b.pre.body.holds g ν := by
  have := b.pre.instantiate g AEnv.dflt ν h
  refine (LFml.holds_agree g _ ?_).mp this
  intro p hp
  simpa only [b.covered p hp, ↓reduceIte] using Parameters.read_assign b.pre.parameters p ν AEnv.dflt

/-- **The leaf is valid exactly where the cut, lifted body is.** -/
theorem valid_iff {ψ : LFml C} (b : ArrayBody ψ) :
    (∀ g, ψ.holds g AEnv.dflt) ↔ b.leaf.Valid := by
  rw [LFml.liftCond_valid]
  have hgx : b.cut.gx.Valid ↔ b.cut.Valid :=
    forall_congr' fun g => forall_congr' fun ν => LFml.gx_holds g b.cut ν
  rw [hgx, LFml.aCut_valid_iff b.hcut (Nat.le_refl _)]
  constructor
  · intro h g ν
    exact (LFml.orLift_holds g orFuel _ ν).mpr (b.holds_body g ν (h g))
  · intro h g
    exact b.pre.close g AEnv.dflt fun ν => (LFml.orLift_holds g orFuel _ ν).mp (h g ν)

/-- **A refutation of the cut body refutes the leaf**, in the state its
arrays are rebuilt in. -/
theorem refutesCut {ψ : LFml C} (b : ArrayBody ψ) (g : State C []) (ν : AEnv)
    (hK : ¬ b.cut.holds g ν) :
    ¬ ψ.holds (realize ν (b.pre.body.orLift orFuel).atomBound b.reads g) AEnv.dflt := by
  intro hψ
  exact LFml.aCut_refutes b.hcut g ν hK
    ((LFml.orLift_holds _ orFuel _ ν).mpr (b.holds_body _ ν hψ))

/-- **A refutation of the arithmetic's leaf refutes the leaf**. -/
theorem refutes {ψ : LFml C} (b : ArrayBody ψ) (g : State C []) (ν : AEnv)
    (h : ¬ b.leaf.holds g ν) :
    ¬ ψ.holds (realize ν (b.pre.body.orLift orFuel).atomBound b.reads g) AEnv.dflt :=
  b.refutesCut g ν fun hk => h ((LFml.liftCond_holds g _ _ ν).mpr ((LFml.gx_holds g _ ν).mpr hk))

/-- The bound on the arrays a countermodel is first looked for in. -/
def smallBound : Nat := 64

/-- **Small arrays**: every live length, every slot that is there and every
slot holding a word other than the default below `smallBound`.  A
countermodel under this premise rebuilds arrays of at most `smallBound`
slots; the arithmetic is free to pick an assignment with lengths near
`2^256` otherwise. -/
def small (N : Nat) (rs : List (ARead C)) : LFml C :=
  LFml.conj ((List.range rs.length).flatMap fun j =>
    match rs[j]? with
    | none => []
    | some r =>
      let B : LTm C (.val .uint) := .app0 (.lit (uintOfNat smallBound))
      match r.kind with
      | .len => [LFml.isT (LTm.ltU (vAt .uint N j) B)]
      | .has => [.imp (LFml.isT (vAt .bool N j)) (LFml.isT (LTm.ltU (r.xTm N j) B))]
      | .word => [.imp (LFml.isF (LTm.ltU (r.xTm N j) B)) (.eq (vAt r.e N j) (LTm.dfltLit r.e))])

/-- The leaf decided for a small countermodel. -/
abbrev smallLeaf {ψ : LFml C} (b : ArrayBody ψ) : LFml C :=
  (LFml.imp (small (b.pre.body.orLift orFuel).atomBound b.reads) b.cut).gx.liftCond condLiftFuel

/-- A refutation of the small leaf refutes the leaf. -/
theorem refutesSmall {ψ : LFml C} (b : ArrayBody ψ) (g : State C []) (ν : AEnv)
    (h : ¬ b.smallLeaf.holds g ν) :
    ¬ ψ.holds (realize ν (b.pre.body.orLift orFuel).atomBound b.reads g) AEnv.dflt :=
  b.refutesCut g ν fun hk =>
    h ((LFml.liftCond_holds g _ _ ν).mpr ((LFml.gx_holds g _ ν).mpr fun _ => hk))

end ArrayBody

/-- The array stages, computed. -/
def arrayBody? (ψ : LFml C) : Option (ArrayBody ψ) := do
  let u ← UniversalPrefix.ofFormula? 1024 ψ
  if hc : ∀ p ∈ u.body.parameters, p ∈ u.parameters then
    if u.body.ors ≤ orBudget then
      match hk : (u.body.orLift orFuel).aCut? (u.body.orLift orFuel).atomBound with
      | some (K, rs) => some ⟨u, hc, K, rs, hk⟩
      | none => none
    else none
  else none

/-- **A leaf that reads storage arrays, decided by arithmetic.** -/
structure ArrayReduction (φ : Fml C []) where
  normalization : DeclarationReduction φ
  source : SourceReduction normalization.formula
  body : ArrayBody source.leaf.elim.condSimp.prenex
  flat : FlattenedArithmetic body.leaf

def arrayReduction? (φ : Fml C []) : Option (ArrayReduction φ) := do
  let d ← ProgramNormalization.ofFormula? 2048 φ
  let r ← sourceReduction? d.formula
  let b ← arrayBody? r.leaf.elim.condSimp.prenex
  -- The lift's size first, within `liftBudget` nodes.
  if (b.cut.gx.liftCondB condLiftFuel liftBudget).isNone then none
  return ⟨d, r, b, ← flattenedArithmetic? 2048 b.leaf⟩

namespace ArrayReduction

theorem leaf_iff {φ : Fml C []} (r : ArrayReduction φ) :
    Fml.Valid φ ↔ ∀ g, r.source.leaf.elim.condSimp.prenex.holds g AEnv.dflt := by
  constructor
  · intro h g
    exact (LFml.prenex_holds g _ _).mpr ((LFml.condSimp_holds g _ _).mpr
      ((r.source.elim_holds_iff g).mpr ((r.normalization.correct g).mpr (h g))))
  · intro h g
    exact (r.normalization.correct g).mp ((r.source.elim_holds_iff g).mp
      ((LFml.condSimp_holds g _ _).mp ((LFml.prenex_holds g _ _).mp (h g))))

theorem valid_iff {φ : Fml C []} (r : ArrayReduction φ) :
    Fml.Valid φ ↔ r.flat.encoding.arithmetic.Valid :=
  r.leaf_iff.trans (r.body.valid_iff.trans r.flat.valid_iff)

structure Countermodel {φ : Fml C []} (r : ArrayReduction φ) where
  state : State C []
  refutes : ¬ holds state φ

def countermodelOf {φ : Fml C []} (r : ArrayReduction φ)
    (cm : {vs // ¬ r.flat.encoding.arithmetic.holds vs}) : r.Countermodel := by
  let actual := r.flat.countermodelOf cm
  refine ⟨realize actual.atoms (r.body.pre.body.orLift orFuel).atomBound r.body.reads actual.state,
    fun hv => r.body.refutes actual.state actual.atoms actual.refutes ?_⟩
  exact (LFml.prenex_holds _ _ _).mpr ((LFml.condSimp_holds _ _ _).mpr
    ((r.source.elim_holds_iff _).mpr ((r.normalization.correct _).mpr hv)))

/-- A countermodel from the small leaf's arithmetic. -/
def countermodelOfSmall {φ : Fml C []} (r : ArrayReduction φ)
    (F : FlattenedArithmetic r.body.smallLeaf)
    (cm : {vs // ¬ F.encoding.arithmetic.holds vs}) : r.Countermodel := by
  let actual := F.countermodelOf cm
  refine ⟨realize actual.atoms (r.body.pre.body.orLift orFuel).atomBound r.body.reads actual.state,
    fun hv => r.body.refutesSmall actual.state actual.atoms actual.refutes ?_⟩
  exact (LFml.prenex_holds _ _ _).mpr ((LFml.condSimp_holds _ _ _).mpr
    ((r.source.elim_holds_iff _).mpr ((r.normalization.correct _).mpr hv)))

/-- **The verdict**: a proof, or a countermodel, looked for first among
small arrays (`ArrayBody.small`). -/
def verify {φ : Fml C []} (r : ArrayReduction φ) : Sum (PLift (Fml.Valid φ)) r.Countermodel :=
  match r.flat.encoding.arithmetic.verify with
  | .inl h => .inl ⟨r.valid_iff.mpr h.down⟩
  | .inr cm =>
    match flattenedArithmetic? 2048 r.body.smallLeaf with
    | some F =>
      match F.encoding.arithmetic.verify with
      | .inr cm' => .inr (r.countermodelOfSmall F cm')
      | .inl _ => .inr (r.countermodelOf cm)
    | none => .inr (r.countermodelOf cm)

end ArrayReduction

/-! ## The fragment -/

/-- **The eliminated leaf's fragment with array reads**: the array stages
succeed, and their leaf is in `LFml.Src true` (the elimination's
conditionals allowed), of lifting weight below `condLiftFuel`, lifted within
the budget and within M4's bounds. -/
def LFml.arrayCovered (ψ : LFml C) : Bool :=
  match arrayBody? ψ with
  | some b =>
    (b.cut.gx.src? true).isSome && decide (b.cut.gx.condMax < condLiftFuel) &&
      (b.cut.gx.liftCondB condLiftFuel liftBudget).isSome &&
      decide (b.leaf.cutAll.nodes ≤ 511) && decide (b.leaf.cutAll.words * b.leaf.cutAll.words ≤ 2048)
  | none => false

/-- **The fragment of the decision with array reads.** -/
def _root_.Solidity.Fml.arrayCovered (φ : Fml C []) : Bool :=
  match leafOf? φ with
  | some ψ => ψ.arrayCovered
  | none => false

/-- **The decision with array reads never refuses its fragment.** -/
theorem arrayReduction?_isSome (φ : Fml C []) (h : φ.arrayCovered = true) :
    (arrayReduction? φ).isSome = true := by
  unfold Fml.arrayCovered at h
  cases hl : leafOf? φ with
  | none => rw [hl] at h; cases h
  | some ψ =>
    rw [hl] at h
    simp only [leafOf?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hl
    obtain ⟨d, hd, r, hr, rfl⟩ := hl
    dsimp only [LFml.arrayCovered] at h
    cases hb : arrayBody? r.leaf.elim.condSimp.prenex with
    | none => rw [hb] at h; cases h
    | some b =>
      rw [hb] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨hsrc, hm⟩, hcap⟩, hn⟩, hw⟩ := h
      obtain ⟨⟨hs⟩, -⟩ := Option.isSome_iff_exists.mp hsrc
      have hlift := LFml.liftCond_src condLiftFuel hs hm
      obtain ⟨F, hF⟩ := Option.isSome_iff_exists.mp (flattenedArithmetic?_isSome b.leaf hlift hn hw)
      have hnone : (b.cut.gx.liftCondB condLiftFuel liftBudget).isNone = false := by
        cases hX : b.cut.gx.liftCondB condLiftFuel liftBudget with
        | none => rw [hX] at hcap; cases hcap
        | some _ => rfl
      simp only [arrayReduction?, hd, hr, hb, Option.bind_eq_bind, Option.bind_some, hnone,
        Bool.false_eq_true, if_false, hF]
      rfl

end Solidity.Decide
