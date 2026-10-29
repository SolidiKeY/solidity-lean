import Solidity.Calculus.Decision
import Solidity.Calculus.HashWrittenInput

/-! # Certified written-memory input cuts
The input helpers live below `Decision` in `HashWrittenInput`. These adapters
compose a supplied intrinsic input certificate with the existing memory cut
and decider. They do not produce general negative-array certificates.
-/
namespace Solidity.Decide.WrittenMemory
variable {C : Contract}

/-- An intrinsic input formula with its scope-correct proof, under the
original formula's premise. This is not a coverage or extraction predicate. -/
structure HashInputReduction (φ : Fml C []) where
  formula : Fml C []
  correct : ∀ σ : State C [], φ.HashFree σ → (Fml.holdsS σ φ ↔ holds σ formula)

namespace HashInputReduction

/-- Composing input reduction with exactly `decideMem`'s existing hoist and
cut. The original finite premise is retained, including binder-local meaning. -/
def cut {φ : Fml C []} (r : HashInputReduction φ) {ψ : Fml C []}
    (hc : (r.formula.hoist 1024).mxTop = some ψ) : HashInputReduction φ :=
  ⟨ψ, fun σ hf => (r.correct σ hf).trans
    ((Fml.hoist_holds 1024 r.formula σ).symm.trans (Fml.mxTop_holds hc σ))⟩

/-- Run the existing memory cut only after a proof-backed input reduction. -/
def cut? {φ : Fml C []} (r : HashInputReduction φ) : Option (HashInputReduction φ) :=
  match hc : (r.formula.hoist 1024).mxTop with
  | none => none
  | some _ψ => some (r.cut hc)

/-- A proof of the cut input leaf proves the original hash formula. -/
theorem sound {φ : Fml C []} (r : HashInputReduction φ) (h : Fml.Valid r.formula) : Fml.ValidH φ :=
  fun σ hf => (r.correct σ hf).2 (h σ)

/-- A false cut leaf refutes the original only with its actual finite
premise; at a collision `holdsH` could instead be vacuously true. -/
theorem refutes {φ : Fml C []} (r : HashInputReduction φ) (σ : State C [])
    (hf : φ.HashFree σ) (hn : ¬ holds σ r.formula) : ¬ Fml.holdsH σ φ :=
  fun h => hn ((r.correct σ hf).1 (h hf))

/-- The existing memory decision can prove a certified hash-input formula. -/
theorem valid_of_decideMem {φ : Fml C []} (r : HashInputReduction φ)
    (h : decideMem r.formula = .proved) : Fml.ValidH φ := r.sound (decideMem_sound h)

/-- Refutation preserves the same prestate and explicitly requires its
original hash premise, rather than assuming collision freedom. -/
theorem refutes_of_decideMem {φ : Fml C []} (r : HashInputReduction φ) {σ : State C []}
    (hf : φ.HashFree σ) (h : decideMem r.formula = .refuted σ) : ¬ Fml.holdsH σ φ :=
  r.refutes σ hf (decideMem_refutes h)

end HashInputReduction

/-- info: 'Solidity.Decide.WrittenMemory.HashInputReduction.cut?' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms HashInputReduction.cut?
/-- info: 'Solidity.Decide.WrittenMemory.HashInputReduction.valid_of_decideMem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms HashInputReduction.valid_of_decideMem
/-- info: 'Solidity.Decide.WrittenMemory.HashInputReduction.refutes_of_decideMem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms HashInputReduction.refutes_of_decideMem

end Solidity.Decide.WrittenMemory
