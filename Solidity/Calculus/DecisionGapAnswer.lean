import Solidity.Calculus.DecisionPartialOrFloor
import Solidity.Calculus.DecisionBlockRefute

/-!
# Certified answers for decided M7 gaps without fresh allocation

One extension point for gap families decided after the given-heap routes:
`givenHeapAnswerWithFixed` consults `gapAnswer?` only on its own miss, and
`Fml.memCovered` admits exactly `Fml.gapCovered` (with no fresh allocation).
A family added here brings its decidable source class, a proved answer or a
constructive countermodel, and the `isSome` lemma; `Calculus/Decision.lean`
need not change again. Families: the nested partial-OR floor
(`Calculus/DecisionPartialOrFloor.lean`) and false literal-bounded blocks
refuted at a threshold region (`Calculus/DecisionBlockRefute.lean`).
-/
namespace Solidity.Decide
variable {C : Contract}

/-- The decided gap families, tried in order. -/
def gapAnswer? (φ : Fml C []) : Option (MemoryWitness.Answer φ) :=
  (ResidueReason.partialOrFloorAnswer? φ).orElse fun _ => BlockRefute.answer? φ

/-- Decidable membership: a syntactic source family, or a certified refutation
found by the finite region search (a semi-decision: membership is the search's
own success). No `decideGoal`/`Covered` verdict is consulted. -/
def _root_.Solidity.Fml.gapCovered (φ : Fml C []) : Bool := φ.partialOrFloor || φ.blockRefutable

/-- Every member of a decided gap family is answered. -/
theorem gapAnswer_isSome {φ : Fml C []} (h : φ.gapCovered = true) : (gapAnswer? φ).isSome = true := by
  unfold gapAnswer?
  cases hp : ResidueReason.partialOrFloorAnswer? φ with
  | some a => rfl
  | none =>
    simp only [Option.orElse_none]
    unfold Fml.gapCovered at h
    cases hf : φ.partialOrFloor with
    | true =>
      have := ResidueReason.partialOrFloorAnswer_isSome hf
      rw [hp] at this
      cases this
    | false =>
      rw [hf, Bool.false_or] at h
      exact BlockRefute.answer_isSome h

end Solidity.Decide
