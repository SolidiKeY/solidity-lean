import Solidity.Calculus.DecisionMappingFieldBoundary
import Solidity.Examples.DecisionResidueReasons

/-! # Inhabited mapping-bearing reversed-field reason controls
Actual source recognition, target admission and producer-schema refusal remain
separate from the global verdicts, which the void-binder route now proves. No missing realization is assumed.
-/
namespace Solidity.Examples.DecisionMappingFieldReason
open Solidity.Decide Solidity.Decide.ResidueReason
open Solidity.Examples.Decision
open Solidity.Examples.DecisionResidueReasons
set_option Elab.async false

def mappingOne : Fml StandardExample [] :=
  cdl[StandardExample]{ ∀ fresh Wallet w; 1 = w.owner }

theorem inhabited_classes : mappingReversed.freshStructMappingReversedPrimitiveEquation = true ∧
    mappingOne.freshStructMappingReversedPrimitiveEquation = true := by decide +kernel

def originalWitness : MappingReversedFreshField mappingReversed :=
  (mappingReversedFreshField? mappingReversed).get (by decide +kernel)

def anotherWitness : MappingReversedFreshField mappingOne :=
  (mappingReversedFreshField? mappingOne).get (by decide +kernel)

theorem both_targets (waivers : Waivers) : mappingReversed.inTarget waivers = true ∧
    mappingOne.inTarget waivers = true :=
  ⟨originalWitness.target waivers, anotherWitness.target waivers⟩

theorem both_hash_free : mappingReversed.hasHash = false ∧ mappingOne.hasHash = false :=
  ⟨originalWitness.hashFree, anotherWitness.hashFree⟩

/-- The exact family proposition has a constructive executable decision. -/
theorem decidable_controls : decide (Nonempty (MappingReversedFreshField mappingReversed)) = true ∧
    decide (Nonempty (MappingReversedFreshField memStructReversed)) = false := by decide +kernel

/-- Supported map-free reversals and distinct map/reflexive/compound/given shapes
are not reclassified by the mapping-bearing reversed source reason. -/
theorem negative_and_combination_controls :
    ([memStructReversed, reversedFive, reversedBool, memStructMapping,
      memStructBuried].map Fml.freshStructMappingReversedPrimitiveEquation).any id = false ∧
    memParamSame.freshStructMappingReversedPrimitiveEquation = false := by
  decide +kernel

/-- These concrete global observations are separate from generic schema refusal:
the producer schema refuses them, and the void-binder route proves them, since a
`Wallet` has no memory object (`Calculus/DecisionMappingStruct.lean`). -/
theorem actual_proved_controls : decideGoal mappingReversed = .proved ∧
    decideGoal mappingOne = .proved := by exact ⟨by rfl, by rfl⟩

/-- A specific existing schema refuses every body of this map-bearing binder. -/
theorem original_schema_boundary (body : Fml StandardExample [.mem (.struct originalWitness.s)]) :
    MemoryWitness.boundAnswer originalWitness.x (.struct originalWitness.s) body = none :=
  originalWitness.schema_refuses body

end Solidity.Examples.DecisionMappingFieldReason
