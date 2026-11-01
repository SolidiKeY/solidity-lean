import Solidity.Calculus.DecisionCompoundFieldReason
import Solidity.Examples.DecisionGapCensus

/-! # Actual compound-RHS gap and exact source-class controls
No existing producer fixture or global observation is changed. The ordinary
countermodel reuses the producer's child heap before parent allocation.
-/
namespace Solidity.Examples.DecisionCompoundFieldReason
open Solidity.Decide Solidity.Decide.ResidueReason
open Solidity.Examples.Decision
set_option Elab.async false

def anotherSum : Fml StandardExample [] :=
  cdl[StandardExample]{ ∀ fresh Person p; p.age = 2 + 3 }

def partialRhs : Fml StandardExample [] :=
  cdl[StandardExample]{ ∀ fresh Person p; p.age = 0 - 1 }

def mappingCompound : Fml StandardExample [] :=
  cdl[StandardExample]{ ∀ fresh Wallet w; w.owner = 0 + 1 }

theorem original_class : memStructBuried.freshStructNonliteralUIntEquation = true := by decide +kernel

theorem another_class : anotherSum.freshStructNonliteralUIntEquation = true := by decide +kernel

theorem partial_class : partialRhs.freshStructNonliteralUIntEquation = true := by decide +kernel

/-- Direct literals, reflexivity, reversal and other primitive sorts remain separate. -/
theorem negative_controls :
    ([memStructFive, memStructSame, memStructReversed, memStructBool, memStructFixed,
      mappingCompound].map Fml.freshStructNonliteralUIntEquation).any id = false := by
  decide +kernel

theorem given_heap_control : memParamSame.freshStructNonliteralUIntEquation = false := by decide +kernel

/-- Existing target admission is wider than the producer map-free schema. -/
theorem mapping_target_control : mappingCompound.inTarget {} = true := by decide +kernel

theorem distinct_reasons :
    memStructReversed.freshStructReversedPrimitiveEquation = true ∧
    memStructReversed.freshStructNonliteralUIntEquation = false ∧
    memStructBuried.freshStructReversedPrimitiveEquation = false ∧
    memStructBuried.freshStructNonliteralUIntEquation = true := by decide +kernel

theorem decidable_positive : decide (Nonempty (NonliteralUIntFreshField memStructBuried)) = true := by
  decide +kernel

theorem decidable_negative : decide (Nonempty (NonliteralUIntFreshField memStructFive)) = false := by
  decide +kernel

def originalWitness : NonliteralUIntFreshField memStructBuried :=
  (nonliteralUIntFreshField? memStructBuried).get (by decide +kernel)

def sum01 {C : Contract} {Γ : Ctx} : Tm C Γ (.val .uint) :=
  .app2 (.binop .add rfl) (.app0 (.lit (uintOfNat 0))) (.app0 (.lit (uintOfNat 1)))

theorem sum01_eval {C : Contract} {Γ : Ctx} (σ : State C Γ) :
    (sum01 : Tm C Γ (.val .uint)).eval σ = some (uintOfNat 1) := by rfl

theorem sum01_denote {C : Contract} {Γ : Ctx} (σ : State C Γ) :
    (sum01 : Tm C Γ (.val .uint)).denote σ = some (uintOfNat 1) :=
  Tm.denote_eval σ sum01 (uintOfNat 1) (sum01_eval σ)

def zeroMinusOne {C : Contract} {Γ : Ctx} : Tm C Γ (.val .uint) :=
  .app2 (.binop .sub rfl) (.app0 (.lit (uintOfNat 0))) (.app0 (.lit (uintOfNat 1)))

theorem partial_rhs_halts {C : Contract} {Γ : Ctx} (σ : State C Γ) :
    (zeroMinusOne : Tm C Γ (.val .uint)).eval σ = none := by rfl

/-- The actual assigned gap is false in the original constructed child heap. -/
theorem original_countermodel : ¬ holds gapMemStruct_state memStructBuried := by
  intro h
  apply MemoryWitness.fieldEq_refutes (s := "Person") (f := "age") (p := .uint)
    (State.init StandardExample)
    (MemoryWitness.children Heap.empty "Person" (by decide)) (by decide)
    (.user "p") (uintOfNat 1)
  intro o
  exact (h o).trans (sum01_denote _)

theorem original_hashFree : memStructBuried.hasHash = false := originalWitness.hashFree

theorem original_countermodelH : ¬ Fml.holdsH gapMemStruct_state memStructBuried :=
  fun h => original_countermodel ((Fml.holdsH_iff gapMemStruct_state memStructBuried original_hashFree).mp h)

theorem original_notValid : ¬ Fml.Valid memStructBuried := by
  intro h
  exact original_countermodel (h gapMemStruct_state)

theorem original_target : memStructBuried.inTarget {} = true := DecisionGapCensus.buriedStruct_target

theorem original_global_unknown : decideGoal memStructBuried = .unknown := DecisionGapCensus.buriedStruct_unknown

theorem original_notCovered : memStructBuried.Covered = false := DecisionGapCensus.buriedStruct_notCovered

end Solidity.Examples.DecisionCompoundFieldReason
