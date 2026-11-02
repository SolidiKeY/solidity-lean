import Solidity.Calculus.DecisionArrayReasons
import Solidity.Examples.DecisionSourceChain

/-! # Inhabited and distinguishing nested-array reason controls
The four source reasons classify actual original gap pins. Direct fixed-array
covered controls remain outside these four reasons. The five valid-instance
fixtures now receive certified positive source-route verdicts.
-/
namespace Solidity.Examples.DecisionArrayReasons
open Solidity.Decide Solidity.Decide.ResidueReason
open Solidity.Examples.DecisionArrayGaps
set_option Elab.async false

def keyGap : ArrayBelowKeyAt belowKey (uintOfNat 3) (uintOfNat 1) :=
  ⟨DecisionSourceInstance.keyWitness, rfl⟩
def fixedKeyGap : ArrayBelowKeyAt fixedBelowKey (uintOfNat 3) (uintOfNat 1) :=
  ⟨DecisionSourceInstance.fixedKeyWitness, rfl⟩
def fieldGap : ArrayBelowFieldAt belowField (uintOfNat 3) (uintOfNat 1) :=
  ⟨DecisionSourceInstance.fieldWitness, rfl⟩
def structGap : ArrayOfStructAt arrayStruct (uintOfNat 3) (uintOfNat 1) :=
  ⟨DecisionSourceInstance.structWitness, rfl⟩
def nestedGap : ArrayOfArrayAt arrayArray (uintOfNat 3) (uintOfNat 1) :=
  ⟨DecisionSourceInstance.nestedWitness, rfl⟩

theorem kind_census : [belowKey, fixedBelowKey, belowField, arrayStruct, arrayArray].map
    (fun φ => sourceArrayKind? φ) =
    [some .belowKey, some .belowKey, some .belowField, some .elementsStruct, some .elementsArray] := by rfl

theorem classified_census : belowKey.arrayBelowKeyAt (uintOfNat 3) (uintOfNat 1) = true ∧
    fixedBelowKey.arrayBelowKeyAt (uintOfNat 3) (uintOfNat 1) = true ∧
    belowField.arrayBelowFieldAt (uintOfNat 3) (uintOfNat 1) = true ∧
    arrayStruct.arrayOfStructAt (uintOfNat 3) (uintOfNat 1) = true ∧
    arrayArray.arrayOfArrayAt (uintOfNat 3) (uintOfNat 1) = true :=
  ⟨arrayLiteralGapAt_complete keyGap, arrayLiteralGapAt_complete fixedKeyGap,
    arrayLiteralGapAt_complete fieldGap, arrayLiteralGapAt_complete structGap,
    arrayLiteralGapAt_complete nestedGap⟩

theorem key_not_field : ¬ Nonempty (ArrayBelowFieldAt belowKey (uintOfNat 3) (uintOfNat 1)) := by
  intro ⟨w⟩
  have h : ArrayGapKind.belowKey = .belowField := keyGap.kind_unique w
  cases h

theorem struct_not_nested : ¬ Nonempty (ArrayOfArrayAt arrayStruct (uintOfNat 3) (uintOfNat 1)) := by
  intro ⟨w⟩
  have h : ArrayGapKind.elementsStruct = .elementsArray := structGap.kind_unique w
  cases h

theorem wrong_bound_refused : belowKey.arrayBelowKeyAt (uintOfNat 2) (uintOfNat 1) = false := by
  decide +kernel

theorem outside_guard_refused : belowKey.arrayBelowKeyAt (uintOfNat 3) (uintOfNat 3) = false := by
  decide +kernel

/-- Direct fixed roots are distinct from every named nested-path source reason. -/
theorem direct_fixed_shapes : sourceArrayKind? fixedBlock = none ∧ sourceArrayKind? fixedBad = none := by
  constructor <;> rfl

theorem direct_fixed_outside (bound value : PrimTy.uint.Denote) (kind : ArrayGapKind) :
    (arrayLiteralGapAt? fixedBlock bound value kind).isSome = false := by
  simp only [arrayLiteralGapAt?, direct_fixed_shapes.1, reduceCtorEq, dite_false, Option.isSome_none]

theorem false_fixed_refused (bound value : PrimTy.uint.Denote) (kind : ArrayGapKind) :
    (arrayLiteralGapAt? fixedBad bound value kind).isSome = false := by
  cases he : (arrayLiteralGapAt? fixedBad bound value kind).isSome with
  | false => rfl
  | true =>
    obtain ⟨w⟩ := arrayLiteralGapAt_witness he
    exact False.elim (fixedBad_notValid w.valid)

theorem inhabited_source : holds DecisionSourceInstance.inhabitedStructState
    DecisionSourceInstance.structAntecedent := DecisionSourceInstance.struct_antecedent_inhabited

theorem actual_source_validity : Fml.ValidH belowKey ∧ Fml.ValidH fixedBelowKey ∧
    Fml.ValidH belowField ∧ Fml.ValidH arrayStruct ∧ Fml.ValidH arrayArray :=
  ⟨keyGap.validH (by decide +kernel), fixedKeyGap.validH (by decide +kernel),
    fieldGap.validH (by decide +kernel), structGap.validH (by decide +kernel),
    nestedGap.validH (by decide +kernel)⟩

theorem source_route_proved : decideGoal arrayStruct = .proved ∧ decideGoal arrayArray = .proved ∧
    decideGoal belowKey = .proved ∧ decideGoal fixedBelowKey = .proved ∧ decideGoal belowField = .proved :=
  DecisionSourceChain.preserved_controls

theorem covered_fixed_targets : fixedBlock.inTarget {} = true ∧ fixedBlock.Covered = true ∧
    fixedBad.inTarget {} = true ∧ fixedBad.Covered = true :=
  ⟨fixedBlock_target, fixedBlock_covered, fixedBad_target, fixedBad_covered⟩

end Solidity.Examples.DecisionArrayReasons
