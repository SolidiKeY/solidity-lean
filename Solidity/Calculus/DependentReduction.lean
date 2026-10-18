import Solidity.Calculus.LeafInputs

/-!
# Original-source decisions with dependent mapping reads

Exact program/update normalization and universal parameter instantiation precede
automatic occurrence flattening. The original body may read only its declared
typed parameters. Generated alias arithmetic then decides validity and
reconstructs an actual counterstate to the original scoped formula.
-/

namespace Solidity.Decide

open ReadRealization Linear ScalarCode

variable {C : Contract}

structure DependentReduction (φ : Fml C []) where
  normalization : DeclarationReduction φ
  source : SourceReduction normalization.formula
  sentence : UniversalPrefix source.leaf.elim
  body : FlattenedArithmetic sentence.body
  covered : ∀ p ∈ sentence.body.parameters, p ∈ sentence.parameters

def dependentReduction? (φ : Fml C []) : Option (DependentReduction φ) := do
  let d ← ProgramNormalization.ofFormula? 2048 φ
  let r ← sourceReduction? d.formula
  let sentence ← UniversalPrefix.ofFormula? 1024 r.leaf.elim
  if hc : ∀ p ∈ sentence.body.parameters, p ∈ sentence.parameters then
    return ⟨d, r, sentence, ← flattenedArithmetic? 2048 sentence.body, hc⟩
  else none

namespace DependentReduction

def arithmetic {φ : Fml C []} (r : DependentReduction φ) :
    TypedFormula (Inputs.types r.body.encoding.environment r.body.encoding.parameters r.body.encoding.refs) :=
  r.body.encoding.arithmetic

theorem body_valid_iff {φ : Fml C []} (r : DependentReduction φ) :
    Valid φ ↔ r.sentence.body.Valid := by
  constructor
  · intro h g ν
    exact (r.body.flattening.source.holds_assign g r.sentence.parameters r.covered AEnv.dflt ν).mp
      (r.sentence.instantiate g AEnv.dflt ν
        ((r.source.elim_holds_iff g).mpr ((r.normalization.correct g).mpr (h g))))
  · intro h g
    exact (r.normalization.correct g).mp ((r.source.elim_holds_iff g).mp
      (r.sentence.close g AEnv.dflt (h g)))

theorem valid_iff {φ : Fml C []} (r : DependentReduction φ) : Valid φ ↔ r.arithmetic.Valid :=
  r.body_valid_iff.trans r.body.valid_iff

theorem valid_of_decide {φ : Fml C []} (r : DependentReduction φ)
    (h : r.arithmetic.guarded.decide = true) : Valid φ :=
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
    (r.sentence.instantiate _ AEnv.dflt actual.atoms
      ((r.source.elim_holds_iff _).mpr ((r.normalization.correct _).mpr hv)))

def checkCodes {φ : Fml C []} (r : DependentReduction φ) (xs : List Nat) : Bool :=
  r.arithmetic.guarded.check (fun k => xs[k]?.getD 0)

def countermodelOfCodes {φ : Fml C []} (r : DependentReduction φ) (xs : List Nat)
    (h : r.checkCodes xs = false) : r.Countermodel :=
  r.countermodelOf (r.arithmetic.countermodelOf (fun k => xs[k]?.getD 0)
    (fun hv => Bool.false_ne_true (h ▸ (AFml.check_iff _ _).mpr hv)))

theorem not_valid_of_codes {φ : Fml C []} (r : DependentReduction φ) (xs : List Nat)
    (h : r.checkCodes xs = false) : ¬ Valid φ :=
  fun hv => (r.countermodelOfCodes xs h).refutes (hv (r.countermodelOfCodes xs h).state)

def verify {φ : Fml C []} (r : DependentReduction φ) : Sum (PLift (Valid φ)) r.Countermodel :=
  match r.arithmetic.verify with
  | .inl h => .inl ⟨r.valid_iff.mpr h.down⟩
  | .inr cm => .inr (r.countermodelOf cm)

end DependentReduction

end Solidity.Decide
