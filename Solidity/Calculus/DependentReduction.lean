import Solidity.Calculus.LeafInputs
import Solidity.Calculus.CondLift

/-!
# Original-source decisions with dependent mapping reads

Exact program/update normalization, the folding and lifting of the
elimination's conditionals into case splits (`Calculus/CondLift.lean`) and universal
parameter instantiation precede automatic occurrence flattening. The original body may read only its declared
typed parameters. Generated alias arithmetic then decides validity and
reconstructs an actual counterstate to the original scoped formula.
-/

namespace Solidity.Decide

open ReadRealization Linear ScalarCode

variable {C : Contract}

/-- The nesting depth to which the elimination's conditionals are lifted. -/
def condLiftFuel : Nat := 64

/-! ## The lift within a node budget

`liftCond` can multiply a formula by three per conditional; the flattener
then refuses anything past 511 nodes.  `LFml.liftCondB` computes the same
lift with a node budget for its result (`LFml.fits`), threading the fuel
left, and stops as soon as the result would exceed it, so a leaf with many
conditionals is refused after work bounded by the budget, not by its
lifted size (`liftBudget`).  It returns the lift exactly when the lift fits
(`LFml.liftCondB_eq`).  `LFml`'s family has no index, so `match` is
kernel-friendly here (Gate G0). -/

/-- The most nodes of a lifted leaf the later stages can take: a universal
prefix shorter than 1024 binders (`UniversalPrefix.ofFormula? 1024`) and a
body within the flattener's 2048-node budget (`flattenedArithmetic? 2048`).
A leaf in `Fml.exactBounded` (511 body nodes) is within it
(`LFml.liftCondB_isSome`, `Calculus/AutoComplete.lean`). -/
def liftBudget : Nat := 1023 + 2048

/-- One node of a budgeted result, its subterms after it: `none` out of
fuel (`fitsNode` at any result type). -/
def nodeB {α : Type} (n : Nat) (k : Nat → Option α) : Option α :=
  match n with
  | 0 => none
  | n + 1 => k n

theorem fitsNode_map {α : Type} (n : Nat) (k : Nat → Option Nat) (F : Nat → α) :
    (fitsNode n k).map F = nodeB n (fun m => (k m).map F) := by
  cases n <;> rfl

/-- `LFml.mapEq` within a node budget: the result and the fuel left, `none`
past it. -/
def LFml.mapEqB (f : {p : PrimTy} → LTm C (.val p) → LTm C (.val p) → Nat → Option (LFml C × Nat)) :
    LFml C → Nat → Option (LFml C × Nat)
  | .tt, n => ((LFml.tt : LFml C).fits n).map (LFml.tt, ·)
  | .eq a b, n => f a b n
  | .not φ, n => nodeB n fun m => (φ.mapEqB f m).map fun r => (LFml.not r.1, r.2)
  | .and φ ψ, n => nodeB n fun m => (φ.mapEqB f m).bind fun r =>
      (ψ.mapEqB f r.2).map fun r' => (LFml.and r.1 r'.1, r'.2)
  | .imp φ ψ, n => nodeB n fun m => (φ.mapEqB f m).bind fun r =>
      (ψ.mapEqB f r.2).map fun r' => (LFml.imp r.1 r'.1, r'.2)
  | .all k p φ, n => nodeB n fun m => (φ.mapEqB f m).map fun r => (LFml.all k p r.1, r.2)

/-- `LFml.liftEq` within a node budget. -/
def LFml.liftEqB (k : LFml C → Nat → Option (LFml C × Nat)) {p : PrimTy} (a b : LTm C (.val p))
    (n : Nat) : Option (LFml C × Nat) :=
  match a.condSplit with
  | some r => k (r.guard.split (.eq r.thn b) (.eq r.els b) (.eq r.bad b)) n
  | none =>
    match b.condSplit with
    | some r => k (r.guard.split (.eq a r.thn) (.eq a r.els) (.eq a r.bad)) n
    | none => ((LFml.eq a b).fits n).map (.eq a b, ·)

/-- **`LFml.liftCond` within a node budget**: `none` as soon as the lifted
formula exceeds it. -/
def LFml.liftCondB : Nat → LFml C → Nat → Option (LFml C × Nat)
  | 0, φ, n => (φ.fits n).map (φ, ·)
  | k + 1, φ, n => φ.mapEqB (LFml.liftEqB (LFml.liftCondB k)) n

theorem LFml.fits_not (φ : LFml C) (n : Nat) : (LFml.not φ).fits n = fitsNode n φ.fits := by
  rw [LFml.fits_eq_fitsM, LFml.fits_eq_fitsM]; rfl

theorem LFml.fits_all (k : Nat) (p : PrimTy) (φ : LFml C) (n : Nat) :
    (LFml.all k p φ).fits n = fitsNode n φ.fits := by
  rw [LFml.fits_eq_fitsM, LFml.fits_eq_fitsM]; rfl

theorem LFml.fits_and (φ ψ : LFml C) (n : Nat) :
    (LFml.and φ ψ).fits n = fitsNode n fun m => (φ.fits m).bind ψ.fits := by
  rw [LFml.fits_eq_fitsM, LFml.fits_eq_fitsM, LFml.fits_eq_fitsM]; rfl

theorem LFml.fits_imp (φ ψ : LFml C) (n : Nat) :
    (LFml.imp φ ψ).fits n = fitsNode n fun m => (φ.fits m).bind ψ.fits := by
  rw [LFml.fits_eq_fitsM, LFml.fits_eq_fitsM, LFml.fits_eq_fitsM]; rfl

theorem LFml.mapEqB_eq (f : {p : PrimTy} → LTm C (.val p) → LTm C (.val p) → Nat → Option (LFml C × Nat))
    (g : {p : PrimTy} → LTm C (.val p) → LTm C (.val p) → LFml C)
    (hf : ∀ {p : PrimTy} (a b : LTm C (.val p)) (n : Nat), f a b n = ((g a b).fits n).map (g a b, ·)) :
    ∀ (φ : LFml C) (n : Nat), φ.mapEqB f n = ((φ.mapEq g).fits n).map (φ.mapEq g, ·)
  | .tt, n => by simp only [LFml.mapEqB, LFml.mapEq]
  | .eq a b, n => by simp only [LFml.mapEqB, LFml.mapEq]; exact hf a b n
  | .not φ, n => by
    simp only [LFml.mapEqB, LFml.mapEqB_eq f g hf φ, Option.map_map, LFml.mapEq, LFml.fits_not,
      fitsNode_map]
    rfl
  | .all k p φ, n => by
    simp only [LFml.mapEqB, LFml.mapEqB_eq f g hf φ, Option.map_map, LFml.mapEq, LFml.fits_all,
      fitsNode_map]
    rfl
  | .and φ ψ, n => by
    simp only [LFml.mapEqB, LFml.mapEqB_eq f g hf φ, LFml.mapEqB_eq f g hf ψ, LFml.mapEq,
      LFml.fits_and, fitsNode_map]
    congr 1
    funext m
    cases (φ.mapEq g).fits m with
    | none => rfl
    | some v =>
      show Option.map _ (Option.map _ ((ψ.mapEq g).fits v)) = Option.map _ ((ψ.mapEq g).fits v)
      cases (ψ.mapEq g).fits v <;> rfl
  | .imp φ ψ, n => by
    simp only [LFml.mapEqB, LFml.mapEqB_eq f g hf φ, LFml.mapEqB_eq f g hf ψ, LFml.mapEq,
      LFml.fits_imp, fitsNode_map]
    congr 1
    funext m
    cases (φ.mapEq g).fits m with
    | none => rfl
    | some v =>
      show Option.map _ (Option.map _ ((ψ.mapEq g).fits v)) = Option.map _ ((ψ.mapEq g).fits v)
      cases (ψ.mapEq g).fits v <;> rfl

/-- **The budgeted lift is the lift**, where it fits the budget. -/
theorem LFml.liftCondB_eq : ∀ (k : Nat) (φ : LFml C) (n : Nat),
    φ.liftCondB k n = ((φ.liftCond k).fits n).map (φ.liftCond k, ·)
  | 0, _, _ => rfl
  | k + 1, φ, n => by
    apply LFml.mapEqB_eq
    intro p a b m
    unfold LFml.liftEqB LFml.liftEq
    cases a.condSplit with
    | some r => exact LFml.liftCondB_eq k _ m
    | none =>
      cases b.condSplit with
      | some r => exact LFml.liftCondB_eq k _ m
      | none => rfl

structure DependentReduction (φ : Fml C []) where
  normalization : DeclarationReduction φ
  source : SourceReduction normalization.formula
  sentence : UniversalPrefix (source.leaf.elim.condSimp.liftCond condLiftFuel)
  body : FlattenedArithmetic sentence.body
  covered : ∀ p ∈ sentence.body.parameters, p ∈ sentence.parameters

def dependentReduction? (φ : Fml C []) : Option (DependentReduction φ) := do
  let d ← ProgramNormalization.ofFormula? 2048 φ
  let r ← sourceReduction? d.formula
  -- The lift's size first, within `liftBudget` nodes: past it the flattener
  -- refuses the leaf, and lifting it whole would be exponential.
  if (r.leaf.elim.condSimp.liftCondB condLiftFuel liftBudget).isNone then none
  let sentence ← UniversalPrefix.ofFormula? 1024 (r.leaf.elim.condSimp.liftCond condLiftFuel)
  if hc : ∀ p ∈ sentence.body.parameters, p ∈ sentence.parameters then
    return ⟨d, r, sentence, ← flattenedArithmetic? 2048 sentence.body, hc⟩
  else none

namespace DependentReduction

def arithmetic {φ : Fml C []} (r : DependentReduction φ) :
    TypedFormula (Inputs.types r.body.encoding.environment r.body.encoding.parameters r.body.encoding.refs) :=
  r.body.encoding.arithmetic

theorem body_valid_iff {φ : Fml C []} (r : DependentReduction φ) :
    Fml.Valid φ ↔ r.sentence.body.Valid := by
  constructor
  · intro h g ν
    exact (r.body.flattening.source.holds_assign g r.sentence.parameters r.covered AEnv.dflt ν).mp
      (r.sentence.instantiate g AEnv.dflt ν ((LFml.liftCond_holds g _ _ _).mpr
        ((LFml.condSimp_holds g _ _).mpr
          ((r.source.elim_holds_iff g).mpr ((r.normalization.correct g).mpr (h g))))))
  · intro h g
    exact (r.normalization.correct g).mp ((r.source.elim_holds_iff g).mp
      ((LFml.condSimp_holds g _ _).mp
        ((LFml.liftCond_holds g _ _ _).mp (r.sentence.close g AEnv.dflt (h g)))))

theorem valid_iff {φ : Fml C []} (r : DependentReduction φ) : Fml.Valid φ ↔ r.arithmetic.Valid :=
  r.body_valid_iff.trans r.body.valid_iff

theorem valid_of_decide {φ : Fml C []} (r : DependentReduction φ)
    (h : r.arithmetic.guarded.decide = true) : Fml.Valid φ :=
  r.valid_iff.mpr (r.arithmetic.valid_iff.mpr ((AFml.decide_iff _).mp h))

structure Countermodel {φ : Fml C []} (r : DependentReduction φ) where
  state : State C []
  atoms : AEnv
  refutes : ¬ holds state φ

def countermodelOf {φ : Fml C []} (r : DependentReduction φ)
    (cm : {vs // ¬ r.arithmetic.holds vs}) : r.Countermodel := by
  let actual := r.body.countermodelOf cm
  refine ⟨actual.state, actual.atoms, fun hv => actual.refutes ?_⟩
  exact (r.body.flattening.source.holds_assign _ r.sentence.parameters r.covered AEnv.dflt _).mp
    (r.sentence.instantiate _ AEnv.dflt actual.atoms ((LFml.liftCond_holds _ _ _ _).mpr
      ((LFml.condSimp_holds _ _ _).mpr
        ((r.source.elim_holds_iff _).mpr ((r.normalization.correct _).mpr hv)))))

def checkCodes {φ : Fml C []} (r : DependentReduction φ) (xs : List Nat) : Bool :=
  r.arithmetic.guarded.check (fun k => xs[k]?.getD 0)

def countermodelOfCodes {φ : Fml C []} (r : DependentReduction φ) (xs : List Nat)
    (h : r.checkCodes xs = false) : r.Countermodel :=
  r.countermodelOf (r.arithmetic.countermodelOf (fun k => xs[k]?.getD 0)
    (fun hv => Bool.false_ne_true (h ▸ (AFml.check_iff _ _).mpr hv)))

theorem not_valid_of_codes {φ : Fml C []} (r : DependentReduction φ) (xs : List Nat)
    (h : r.checkCodes xs = false) : ¬ Fml.Valid φ :=
  fun hv => (r.countermodelOfCodes xs h).refutes (hv (r.countermodelOfCodes xs h).state)

def verify {φ : Fml C []} (r : DependentReduction φ) : Sum (PLift (Fml.Valid φ)) r.Countermodel :=
  match r.arithmetic.verify with
  | .inl h => .inl ⟨r.valid_iff.mpr h.down⟩
  | .inr cm => .inr (r.countermodelOf cm)

end DependentReduction

end Solidity.Decide
