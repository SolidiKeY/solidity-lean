import Solidity.Calculus.DecisionGivenHeapBoundary
import Solidity.Calculus.DecisionGivenHeapComputedBoundary
import Solidity.Examples.DecisionGapCensus

/-! # Inhabited given-heap source certificates and refusal controls
The all-heap Answer now reaches the real global pipeline. Source classification
remains independent of all coverage and verdict observations.
-/
namespace Solidity.Examples.DecisionGivenHeapReason
open Solidity.Decide Solidity.Decide.ResidueReason
open Solidity.Examples.Decision
local instance givenHeapContract : InContract := ⟨Gaps⟩
open scoped Solidity.Scoped
set_option Elab.async false

def anotherIndex : Fml Gaps [] := dl![.box]{ s[1] = s[1] where uint[] memory s }
def differentKeys : Fml Gaps [] := dl![.box]{ s[0] = s[1] where uint[] memory s }
def nonliteralIndex : Fml Gaps [] := dl![.box]{ s[0 + 1] = s[0 + 1] where uint[] memory s }
def literalReflexive : Fml Gaps [] := dl![.box]{ 0 = 0 where uint[] memory s }
def diamondReflexive : Fml Gaps [] := dl![.diamond]{ s[0] = s[0] where uint[] memory s }
def freshReflexive : Fml Gaps [] := cdl[Gaps]{ ∀ fresh uint[] s; s[0] = s[0] }

/-- The existing valid given-heap pin and a genuinely different literal index classify. -/
theorem positive_classes : memParamSame.givenHeapLiteralReadReflexive = true ∧
    anotherIndex.givenHeapLiteralReadReflexive = true := by decide +kernel

/-- Full-term comparison refuses unequal reads, computed keys and different binders. -/
theorem negative_classes :
    ([differentKeys, nonliteralIndex, literalReflexive,
      freshReflexive, gapMemParam, memParamAliasBad].map Fml.givenHeapLiteralReadReflexive).any id = false := by
  decide +kernel

/-- Existing leaf-only notation does not materialize a diamond binder here.
This exact identity records the surprising source; no default/notation is changed. -/
theorem diamondNotation_same_source : diamondReflexive = memParamSame := by rfl

/-- The generated source is positive, while an actual diamond binder is generically refused. -/
theorem diamondNotation_class : diamondReflexive.givenHeapLiteralReadReflexive = true := by
  rw [diamondNotation_same_source]
  exact positive_classes.1

/-- A computable witness from the actual source parser, without choice. -/
def originalWitness : GivenHeapLiteralReadReflexive memParamSame :=
  (givenHeapLiteralRead? memParamSame).get (by decide +kernel)

def anotherWitness : GivenHeapLiteralReadReflexive anotherIndex :=
  (givenHeapLiteralRead? anotherIndex).get (by decide +kernel)

/-- The certificate quantifies over every heap, not the producer's finite candidate. -/
theorem original_valid : Fml.Valid memParamSame := originalWitness.valid

theorem another_valid : Fml.Valid anotherIndex := anotherWitness.valid

theorem original_validH : Fml.ValidH memParamSame := originalWitness.validH

theorem actual_targets : memParamSame.inTarget {} = true ∧ anotherIndex.inTarget {} = true :=
  ⟨originalWitness.target {}, anotherWitness.target {}⟩

/-- A proved Answer is available without promoting the result at one heap. -/
theorem original_answer_component : Nonempty (MemoryWitness.Answer memParamSame) :=
  ⟨originalWitness.answer⟩

/-- Exact witness-family decisions have both inhabited positive and negative controls. -/
theorem decidable_controls :
    decide (Nonempty (GivenHeapLiteralReadReflexive memParamSame)) = true ∧
    decide (Nonempty (GivenHeapLiteralReadReflexive gapMemParam)) = false := by
  decide +kernel

/-- Classification refusal is not a claim that the source is invalid. -/
theorem valid_refusals : Fml.Valid nonliteralIndex ∧ Fml.Valid literalReflexive := by
  constructor
  · intro σ v
    rfl
  · intro σ v
    rfl

/-- Actual global positive results follow from the complete source route. -/
theorem original_proved : decideGoal memParamSame = .proved := originalWitness.proved

theorem another_proved : decideGoal anotherIndex = .proved := anotherWitness.proved

theorem original_covered : memParamSame.Covered = true := originalWitness.covered

theorem another_covered : anotherIndex.Covered = true := anotherWitness.covered

/-- The literal classifier still refuses this assigned gap; the new typed route proves it. -/
def computedWitness : GivenHeapLinearReadReflexive nonliteralIndex :=
  (givenHeapLinearRead? nonliteralIndex).get (by decide +kernel)

theorem computed_index_proved : decideGoal nonliteralIndex = .proved := computedWitness.proved

theorem computed_index_covered : nonliteralIndex.Covered = true := computedWitness.covered

/-- The existing nonempty-heap and alias countermodels remain certified. -/
theorem retained_countermodels :
    ¬ holds (MemoryWitness.candidate Gaps) gapMemParam ∧
    ¬ holds (MemoryWitness.candidate Gaps) memParamAliasBad :=
  ⟨gapMemParam_countermodel, memParamAliasBad_countermodel⟩

/-- Both old negative controls return exactly the existing candidate heap. -/
theorem retained_param_verdict :
    decideGoal gapMemParam = .refuted (MemoryWitness.candidate Gaps) :=
  givenHeapCandidate_route (by rfl) (by rfl) (by rfl) (by decide +kernel)

theorem retained_alias_verdict :
    decideGoal memParamAliasBad = .refuted (MemoryWitness.candidate Gaps) :=
  givenHeapCandidate_route (by rfl) (by rfl) (by rfl) (by decide +kernel)

/-- Certify the actual returned negative controls under the unchanged hash reading. -/
theorem retained_returned_refutations :
    ¬ Fml.holdsH (MemoryWitness.candidate Gaps) gapMemParam ∧
    ¬ Fml.holdsH (MemoryWitness.candidate Gaps) memParamAliasBad :=
  ⟨decideGoal_refutes retained_param_verdict, decideGoal_refutes retained_alias_verdict⟩

/-- Actual candidate identity0 has one uint word; it is not a fresh allocation. -/
def candidateReference : HRef (MemoryWitness.candidate Gaps).H (.array (.prim .uint)) :=
  ⟨0, by rfl⟩

def presentState : State Gaps [.mem (.array (.prim .uint))] :=
  (MemoryWitness.candidate Gaps).push (some candidateReference)

def unsetState : State Gaps [.mem (.array (.prim .uint))] :=
  (State.init Gaps).push (t := .mem (.array (.prim .uint))) none

def readAt (key : PrimTy.uint.Denote) : Tm Gaps [.mem (.array (.prim .uint))] (.val .uint) :=
  (MxObs.read (q := .uint) key).tm

/-- The certificate handles a defined read, an out-of-bounds read, and unset. -/
theorem read_definedness_controls :
    (readAt (uintOfNat 0)).eval presentState = some (uintOfNat 1) ∧
    (readAt (uintOfNat 1)).eval presentState = none ∧
    (readAt (uintOfNat 0)).eval unsetState = none := by
  decide +kernel

/-- Both empty and concrete nonempty heaps satisfy the globally certified sources. -/
theorem actual_states_valid : holds (State.init Gaps) memParamSame ∧
    holds (MemoryWitness.candidate Gaps) anotherIndex :=
  ⟨originalWitness.valid _, anotherWitness.valid _⟩

end Solidity.Examples.DecisionGivenHeapReason
