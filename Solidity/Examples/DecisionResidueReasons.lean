import Solidity.Calculus.DecisionResidueReasons
import Solidity.Examples.DecisionGapCensus

/-! # Inhabited structural reasons, separate from decision observations
The source classifier does not call the decider. Its exact typed witness gives
a constructive refutation component; the global route remains unchanged here.
-/
namespace Solidity.Examples.DecisionResidueReasons
open Solidity.Decide Solidity.Decide.ResidueReason
open Solidity.Examples.Decision
set_option Elab.async false

def reversedFive : Fml StandardExample [] :=
  cdl[StandardExample]{ ∀ fresh Person p; 5 = p.age }

def reversedBool : Fml StandardExample [] :=
  cdl[StandardExample]{ ∀ fresh Toggle t; false = t.on }

def mappingReversed : Fml StandardExample [] :=
  cdl[StandardExample]{ ∀ fresh Wallet w; 0 = w.owner }

theorem original_class : memStructReversed.freshStructReversedPrimitiveEquation = true := by
  decide +kernel

theorem another_literal_class : reversedFive.freshStructReversedPrimitiveEquation = true := by
  decide +kernel

theorem boolean_class : reversedBool.freshStructReversedPrimitiveEquation = true := by
  decide +kernel

/-- The class is neither one fixture nor all fresh-memory equations. -/
theorem supported_and_other_gap_controls :
    ([memStructSame, memStructFive, memStructBool, memStructFixed, memStructBuried,
      memStructMapping, mappingReversed].map Fml.freshStructReversedPrimitiveEquation).any id = false := by
  decide +kernel

theorem given_heap_control : memParamSame.freshStructReversedPrimitiveEquation = false := by
  decide +kernel

/-- Target admission is wider than the producer map-free guard. Neither changes here. -/
theorem mapping_target_control : mappingReversed.inTarget {} = true := by decide +kernel

theorem new_source_targets : reversedFive.inTarget {} = true ∧ reversedBool.inTarget {} = true := by
  decide +kernel

/-- The witness is obtained from the actual computable parser, without choice. -/
def originalWitness : ReversedFreshField memStructReversed :=
  (reversedFreshField? memStructReversed).get (by decide +kernel)

def originalState : State StandardExample [] :=
  originalWitness.counterState (State.init StandardExample)

/-- Reversal retains exactly the producer's child-heap state before parent allocation. -/
theorem producer_state_reused : originalState = gapMemStruct_state := by rfl

theorem original_refuted_at_state : ¬ holds originalState memStructReversed :=
  originalWitness.counterState_refutes (State.init StandardExample)

theorem original_refutedH_at_state : ¬ Fml.holdsH originalState memStructReversed :=
  originalWitness.counterState_refutesH (State.init StandardExample)

theorem original_notValid : ¬ Fml.Valid memStructReversed := by
  intro h
  exact original_refuted_at_state (h originalState)

/-- A certificate component exists even while the old global route misses it. -/
theorem original_answer_component : Nonempty (MemoryWitness.Answer memStructReversed) :=
  ⟨originalWitness.answer⟩

theorem original_target : memStructReversed.inTarget {} = true := DecisionGapCensus.reversedStruct_target

theorem original_global_unknown : decideGoal memStructReversed = .unknown :=
  DecisionGapCensus.reversedStruct_unknown

theorem original_notCovered : memStructReversed.Covered = false := DecisionGapCensus.reversedStruct_notCovered

/-- Existing supported syntax is not reclassified as this gap reason. -/
theorem covered_control : memStructSame.Covered = true ∧
    memStructSame.freshStructReversedPrimitiveEquation = false := by
  exact ⟨memStructSame_covered, by decide +kernel⟩

/-- The exact witness-family proposition has an executable constructive decision. -/
theorem decidable_positive : decide (Nonempty (ReversedFreshField memStructReversed)) = true := by
  decide +kernel

theorem decidable_negative : decide (Nonempty (ReversedFreshField memStructBuried)) = false := by
  decide +kernel

end Solidity.Examples.DecisionResidueReasons
