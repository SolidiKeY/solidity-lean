import Solidity.Calculus.DecisionSourceChain
import Solidity.Examples.DecisionSourceInstance

/-! # Actual array source-chain preparation clients
This checks the new preparation producer without registering it globally;
existing unknown/refutation observations and original storage controls remain.
-/
namespace Solidity.Examples.DecisionSourceChain
open Solidity.Decide
open Solidity.Examples.DecisionArrayGaps
open Solidity.Examples.DecisionSourceInstance
set_option Elab.async false

theorem struct_prepared : ∃ r : DeclarationReduction arrayStruct,
    sourceUIntLiteralReduction? arrayStruct (uintOfNat 3) (uintOfNat 1) = some r ∧
      r.formula = .tt ∧ ∀ σ : State Probe [], holds σ r.formula ↔ holds σ arrayStruct :=
  sourceUIntLiteralReduction_complete structWitness

theorem nested_prepared : ∃ r : DeclarationReduction arrayArray,
    sourceUIntLiteralReduction? arrayArray (uintOfNat 3) (uintOfNat 1) = some r ∧
      r.formula = .tt ∧ ∀ σ : State Probe [], holds σ r.formula ↔ holds σ arrayArray :=
  sourceUIntLiteralReduction_complete nestedWitness

theorem key_prepared : ∃ r : DeclarationReduction belowKey,
    sourceUIntLiteralReduction? belowKey (uintOfNat 3) (uintOfNat 1) = some r ∧
      r.formula = .tt ∧ ∀ σ : State Probe [], holds σ r.formula ↔ holds σ belowKey :=
  sourceUIntLiteralReduction_complete keyWitness

theorem fixed_key_prepared : ∃ r : DeclarationReduction fixedBelowKey,
    sourceUIntLiteralReduction? fixedBelowKey (uintOfNat 3) (uintOfNat 1) = some r ∧
      r.formula = .tt ∧ ∀ σ : State Probe [], holds σ r.formula ↔ holds σ fixedBelowKey :=
  sourceUIntLiteralReduction_complete fixedKeyWitness

theorem field_prepared : ∃ r : DeclarationReduction belowField,
    sourceUIntLiteralReduction? belowField (uintOfNat 3) (uintOfNat 1) = some r ∧
      r.formula = .tt ∧ ∀ σ : State Probe [], holds σ r.formula ↔ holds σ belowField :=
  sourceUIntLiteralReduction_complete fieldWitness

/-- The source premise holds at the already constructed actual three-cell state. -/
theorem inhabited_original_antecedent : holds inhabitedStructState structAntecedent :=
  struct_antecedent_inhabited

/-- Actual false source model excludes a hit for every supplied parameter pair. -/
theorem false_preparation_refused (bound value : PrimTy.uint.Denote) :
    (sourceUIntLiteralReduction? fixedBad bound value).isSome = false := by
  cases he : (sourceUIntLiteralReduction? fixedBad bound value).isSome with
  | false => rfl
  | true =>
    obtain ⟨w⟩ := sourceUIntLiteralReduction_iff.mp he
    exact False.elim (fixedBad_notValid w.valid)

theorem mismatched_control :
    (sourceUIntLiteralReduction? fixedBad (uintOfNat 2) (uintOfNat 1)).isSome = false :=
  false_preparation_refused _ _

theorem outside_guard_control :
    (sourceUIntLiteralReduction? fixedBad (uintOfNat 2) (uintOfNat 2)).isSome = false :=
  false_preparation_refused _ _

theorem preserved_controls :
    decideGoal arrayStruct = .unknown ∧ decideGoal arrayArray = .unknown ∧
    decideGoal belowKey = .unknown ∧ decideGoal fixedBelowKey = .unknown ∧
    decideGoal belowField = .unknown := preserved_global_unknowns

theorem raw_leaf_refusals : leafOf? arrayStruct = none ∧ leafOf? arrayArray = none :=
  before_leaf_translation

/-- Explicit parameterized-family completeness also covers the actual prefixes. -/
theorem actual_chain_classification :
    (sourceUIntLiteralChain? arrayStruct (uintOfNat 3) (uintOfNat 1)).isSome = true ∧
    (sourceUIntLiteralChain? arrayArray (uintOfNat 3) (uintOfNat 1)).isSome = true :=
  ⟨sourceUIntLiteralChain_complete structWitness, sourceUIntLiteralChain_complete nestedWitness⟩

end Solidity.Examples.DecisionSourceChain
