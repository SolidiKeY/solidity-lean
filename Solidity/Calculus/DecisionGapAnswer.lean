import Solidity.Calculus.DecisionPartialOrFloor

/-!
# Certified answers for decided M7 gaps without fresh allocation

One extension point for gap families decided after the given-heap routes:
`givenHeapAnswerWithFixed` consults `gapAnswer?` only on its own miss, and
`Fml.memCovered` admits exactly `Fml.gapCovered` (with no fresh allocation).
A family added here brings its decidable source class, a proved answer or a
constructive countermodel, and the `isSome` lemma; `Calculus/Decision.lean`
need not change again. Families: the nested partial-OR floor
(`Calculus/DecisionPartialOrFloor.lean`).
-/
namespace Solidity.Decide
variable {C : Contract}

/-- The decided gap families, tried in order. -/
def gapAnswer? (φ : Fml C []) : Option (MemoryWitness.Answer φ) :=
  ResidueReason.partialOrFloorAnswer? φ

/-- Decidable membership in a decided gap family; no verdict is consulted. -/
def _root_.Solidity.Fml.gapCovered (φ : Fml C []) : Bool := φ.partialOrFloor

/-- Every member of a decided gap family is answered. -/
theorem gapAnswer_isSome {φ : Fml C []} (h : φ.gapCovered = true) : (gapAnswer? φ).isSome = true :=
  ResidueReason.partialOrFloorAnswer_isSome h

end Solidity.Decide
