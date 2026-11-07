import Solidity.Calculus.DecisionGivenHeapComputedBoundary
import Solidity.Calculus.Surface
import Solidity.Examples.DecisionGapData

/-! # Actual nonliteral given-heap gap controls
The first formula retains the original computed-index gap syntax and contract.
The all-heap source certificate now reaches actual coverage and proved verdicts;
read-definedness, unequal-read and syntactic refusal controls remain intact.
-/
namespace Solidity.Examples.DecisionGivenHeapComputedReason
open Solidity.Decide Solidity.Decide.ResidueReason Solidity.Examples.Decision
local instance computedReasonContract : InContract := ⟨Gaps⟩
open scoped Solidity.Scoped
set_option Elab.async false

def computedIndex : Fml Gaps [] := dl![.box]{ s[0 + 1] = s[0 + 1] where uint[] memory s }
def presentIndex : Fml Gaps [] := dl![.box]{ s[0 + 0] = s[0 + 0] where uint[] memory s }
def partialIndex : Fml Gaps [] := dl![.box]{ s[0 - 1] = s[0 - 1] where uint[] memory s }
def literalIndex : Fml Gaps [] := dl![.box]{ s[0] = s[0] where uint[] memory s }
def differentReads : Fml Gaps [] := dl![.box]{ s[0 + 0] = s[0 + 1] where uint[] memory s }
def nonRead : Fml Gaps [] := dl![.box]{ 0 + 1 = 0 + 1 where uint[] memory s }

def computedWitness : GivenHeapLinearReadReflexive computedIndex :=
  (givenHeapLinearRead? computedIndex).get (by decide +kernel)
def presentWitness : GivenHeapLinearReadReflexive presentIndex :=
  (givenHeapLinearRead? presentIndex).get (by decide +kernel)
def partialWitness : GivenHeapLinearReadReflexive partialIndex :=
  (givenHeapLinearRead? partialIndex).get (by decide +kernel)

theorem positive_classes : computedIndex.givenHeapLinearReadReflexive = true ∧
    presentIndex.givenHeapLinearReadReflexive = true ∧
    partialIndex.givenHeapLinearReadReflexive = true :=
  ⟨givenHeapLinearRead_complete computedWitness, givenHeapLinearRead_complete presentWitness,
    givenHeapLinearRead_complete partialWitness⟩

theorem actual_validity : Fml.Valid computedIndex ∧ Fml.Valid presentIndex ∧
    Fml.Valid partialIndex := ⟨computedWitness.valid, presentWitness.valid, partialWitness.valid⟩

theorem actual_hash_validity : Fml.ValidH computedIndex ∧ Fml.ValidH presentIndex ∧
    Fml.ValidH partialIndex := ⟨computedWitness.validH, presentWitness.validH, partialWitness.validH⟩

theorem actual_targets (waivers : Waivers) : computedIndex.inTarget waivers = true ∧
    presentIndex.inTarget waivers = true ∧ partialIndex.inTarget waivers = true :=
  ⟨computedWitness.target waivers, presentWitness.target waivers, partialWitness.target waivers⟩

/-- The reproduced assigned gap now has a global kernel-certified verdict. -/
theorem computed_proved : decideGoal computedIndex = .proved := computedWitness.proved

theorem computed_covered : computedIndex.Covered = true := computedWitness.covered

theorem companion_proved : decideGoal presentIndex = .proved ∧
    decideGoal partialIndex = .proved := ⟨presentWitness.proved, partialWitness.proved⟩

theorem companion_covered : presentIndex.Covered = true ∧ partialIndex.Covered = true :=
  ⟨presentWitness.covered, partialWitness.covered⟩

theorem new_old_family_disjoint : computedIndex.givenHeapLiteralReadReflexive = false ∧
    literalIndex.givenHeapLiteralReadReflexive = true ∧
    literalIndex.givenHeapLinearReadReflexive = false :=
  ⟨computedWitness.not_literal, by decide +kernel, by decide +kernel⟩

def keyZero : Tm Gaps [.mem (.array (.prim .uint))] (.val .uint) :=
  .app2 (.binop .add rfl) (.app0 (.lit (uintOfNat 0))) (.app0 (.lit (uintOfNat 0)))
def keyOne : Tm Gaps [.mem (.array (.prim .uint))] (.val .uint) :=
  .app2 (.binop .add rfl) (.app0 (.lit (uintOfNat 0))) (.app0 (.lit (uintOfNat 1)))
def keyPartial : Tm Gaps [.mem (.array (.prim .uint))] (.val .uint) :=
  .app2 (.binop .sub rfl) (.app0 (.lit (uintOfNat 0))) (.app0 (.lit (uintOfNat 1)))

def actualDiamond : Fml Gaps [] := .bind .diamond (.user "s") (.mem (.array (.prim .uint)))
  (.eq (computedHeapUIntRead keyOne) (computedHeapUIntRead keyOne))
def actualFresh : Fml Gaps [] := .allocAll (.user "s") (.array (.prim .uint))
  (.eq (computedHeapUIntRead keyOne) (computedHeapUIntRead keyOne))
def fixedBinder : Fml Gaps [] := .bind .box (.user "s") (.mem (.fixed (.prim .uint) 3)) .tt

theorem negative_classes :
    ([literalIndex, differentReads, nonRead, actualDiamond, actualFresh, fixedBinder].map
      Fml.givenHeapLinearReadReflexive).any id = false := by decide +kernel

/-- A real contextual local is covered by the generic source grammar. -/
def contextualKey : Tm Gaps [.mem (.array (.prim .uint)), .val .uint] (.val .uint) :=
  .pvV (.there .here)
def contextualSource : Fml Gaps [.val .uint] :=
  .bind .box (.user "s") (.mem (.array (.prim .uint)))
    (.eq (computedHeapUIntRead contextualKey) (computedHeapUIntRead contextualKey))
def nonlinearKey : Tm Gaps [.mem (.array (.prim .uint)), .val .uint] (.val .uint) :=
  .app2 (.binop .mul rfl) contextualKey contextualKey
def nonlinearSource : Fml Gaps [.val .uint] :=
  .bind .box (.user "s") (.mem (.array (.prim .uint)))
    (.eq (computedHeapUIntRead nonlinearKey) (computedHeapUIntRead nonlinearKey))

theorem contextual_positive : contextualSource.givenHeapLinearReadReflexive = true := by
  decide +kernel

theorem nonlinear_refusal : nonlinearSource.givenHeapLinearReadReflexive = false := by
  decide +kernel

/-- Validity alone does not define membership in the syntactic reason. -/
theorem nonlinear_still_theory_valid : ∀ σ : State Gaps [.val .uint], holds σ nonlinearSource := by
  intro σ v
  rfl

def candidateReference : HRef (MemoryWitness.candidate Gaps).H (.array (.prim .uint)) :=
  ⟨0, by rfl⟩
def presentState : State Gaps [.mem (.array (.prim .uint))] :=
  (MemoryWitness.candidate Gaps).push (some candidateReference)
def unsetState : State Gaps [.mem (.array (.prim .uint))] :=
  (State.init Gaps).push (t := .mem (.array (.prim .uint))) none

/-- Distinguish a defined value, bounds failure, checked-arithmetic failure and unset. -/
theorem read_definedness_controls :
    (computedHeapUIntRead keyZero).eval presentState = some (uintOfNat 1) ∧
    (computedHeapUIntRead keyOne).eval presentState = none ∧
    (computedHeapUIntRead keyPartial).eval presentState = none ∧
    (computedHeapUIntRead keyZero).eval unsetState = none := by
  decide +kernel

/-- Both an empty heap and the actual nonempty candidate satisfy the source formula. -/
theorem inhabited_heap_controls : holds (State.init Gaps) computedIndex ∧
    holds (MemoryWitness.candidate Gaps) presentIndex :=
  ⟨computedWitness.valid _, presentWitness.valid _⟩

def distinctState : State Gaps [] :=
  MemoryWitness.state Gaps (p := .uint) [⟨[uintOfNat 1, uintOfNat 2], by decide⟩]
def distinctReference : HRef distinctState.H (.array (.prim .uint)) := ⟨0, by rfl⟩
def distinctPresent : State Gaps [.mem (.array (.prim .uint))] :=
  distinctState.push (some distinctReference)

/-- Both reads of the unequal-index control are defined and observably different. -/
theorem distinct_reads_defined :
    (computedHeapUIntRead keyZero).eval distinctPresent = some (uintOfNat 1) ∧
    (computedHeapUIntRead keyOne).eval distinctPresent = some (uintOfNat 2) := by
  decide +kernel

/-- Use the existing bridge only where both actual evaluator readings return. -/
theorem different_reads_countermodel : ¬ holds distinctState differentReads := by
  intro h
  have hobs : holds distinctPresent
      (.eq (computedHeapUIntRead keyZero) (computedHeapUIntRead keyOne)) := h (some distinctReference)
  have heq : uintOfNat 1 = uintOfNat 2 :=
    (holds_eq_of_eval distinct_reads_defined.1 distinct_reads_defined.2).mp hobs
  exact (by decide : uintOfNat 1 ≠ uintOfNat 2) heq

end Solidity.Examples.DecisionGivenHeapComputedReason
