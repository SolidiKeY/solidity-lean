import Solidity.Calculus.DecisionMemoryCoverage
import Solidity.Calculus.DecisionGivenHeapBoundary
import Solidity.Calculus.Surface
import Solidity.Examples.Decision

/-! # Concrete clients of the complete memory decision producer
Actual source witnesses feed the global coverage and certified verdict routes.
The original predicates and goal hash interpretation are unchanged.
-/
namespace Solidity.Examples.DecisionMemoryCoverageClient
open Solidity.Decide Solidity.Decide.ResidueReason Solidity.Examples.Decision
local instance memoryClientContract : InContract := ⟨Gaps⟩
open scoped Solidity.Scoped
set_option Elab.async false

/-- A reversed equation over an actual map-free fresh struct. -/
def reversed : Fml Gaps [] := cdl[Gaps]{ ∀ fresh Acc s; 0 = s.v }
/-- Every given heap and every bound array value satisfy repeated Theory reads. -/
def given : Fml Gaps [] := dl![.box]{ s[0] = s[0] where uint[] memory s }
/-- The opposite equation direction is outside the reversed-source recognizer. -/
def forward : Fml Gaps [] := cdl[Gaps]{ ∀ fresh Acc s; s.v = 0 }

theorem reversed_recognized : (reversedFreshField? reversed).isSome = true := by
  rfl

theorem given_recognized : (givenHeapLiteralRead? given).isSome = true := by
  rfl

def reversedWitness : ReversedFreshField reversed :=
  (reversedFreshField? reversed).get reversed_recognized

def givenWitness : GivenHeapLiteralReadReflexive given :=
  (givenHeapLiteralRead? given).get given_recognized

/-- Coverage follows from exact source syntax, with no supplied coverage premise. -/
theorem reversed_covered : reversed.Covered = true := reversedWitness.covered

/-- Admission retains every existing waiver setting. -/
theorem reversed_target (waivers : Waivers) : reversed.inTarget waivers = true :=
  reversedWitness.target waivers

/-- The global route returns a real certified countermodel. -/
theorem reversed_refuted : ∃ state : State Gaps [],
    decideGoal reversed = .refuted state ∧ ¬ Fml.holdsH state reversed :=
  reversedWitness.refuted

/-- The constructed source counterstate independently refutes the same hash reading. -/
theorem source_countermodel :
    ¬ Fml.holdsH (reversedWitness.counterState (State.init Gaps)) reversed :=
  reversedWitness.counterState_refutesH _

/-- The given-heap global result is a positive certificate, not one witness evaluation. -/
theorem given_proved : decideGoal given = .proved := givenWitness.proved

theorem given_validH : Fml.ValidH given := decideGoal_sound given_proved

/-- Rejecting the other source direction does not claim a global unknown verdict. -/
theorem forward_not_reversed : forward.freshStructReversedPrimitiveEquation = false := by
  rfl

end Solidity.Examples.DecisionMemoryCoverageClient
