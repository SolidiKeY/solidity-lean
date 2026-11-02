import Solidity.Calculus.DecisionSourceDiscovery
import Solidity.Examples.DecisionSourceChain

/-! # Actual parameter-free source discovery controls
Five original array fixtures reuse their already-proved chain/heap witnesses.
Global verdict pins remain unchanged: this is a preparation-stage checkpoint.
-/
namespace Solidity.Examples.DecisionSourceDiscovery
open Solidity.Decide Solidity.Examples.DecisionArrayGaps
open Solidity.Examples.DecisionSourceInstance

/-- The real instance indices occur in the original source syntax. -/
theorem fixture_values :
    uintOfNat 1 ∈ sourceUIntDiscoveryValues arrayStruct ∧
    uintOfNat 1 ∈ sourceUIntDiscoveryValues arrayArray ∧
    uintOfNat 1 ∈ sourceUIntDiscoveryValues belowKey ∧
    uintOfNat 1 ∈ sourceUIntDiscoveryValues fixedBelowKey ∧
    uintOfNat 1 ∈ sourceUIntDiscoveryValues belowField := by
  decide +kernel

theorem discovered_fixtures :
    (sourceUIntLiteralDiscovery? arrayStruct).isSome = true ∧
    (sourceUIntLiteralDiscovery? arrayArray).isSome = true ∧
    (sourceUIntLiteralDiscovery? belowKey).isSome = true ∧
    (sourceUIntLiteralDiscovery? fixedBelowKey).isSome = true ∧
    (sourceUIntLiteralDiscovery? belowField).isSome = true :=
  ⟨sourceUIntLiteralDiscovery_complete structWitness fixture_values.1,
    sourceUIntLiteralDiscovery_complete nestedWitness fixture_values.2.1,
    sourceUIntLiteralDiscovery_complete keyWitness fixture_values.2.2.1,
    sourceUIntLiteralDiscovery_complete fixedKeyWitness fixture_values.2.2.2.1,
    sourceUIntLiteralDiscovery_complete fieldWitness fixture_values.2.2.2.2⟩

theorem struct_prepared : ∃ r : DeclarationReduction arrayStruct,
    sourceUIntLiteralPreparation? arrayStruct = some r ∧ r.formula = .tt ∧
      ∀ σ : State Probe [], holds σ r.formula ↔ holds σ arrayStruct :=
  sourceUIntLiteralPreparation_complete structWitness fixture_values.1

theorem nested_prepared : ∃ r : DeclarationReduction arrayArray,
    sourceUIntLiteralPreparation? arrayArray = some r ∧ r.formula = .tt ∧
      ∀ σ : State Probe [], holds σ r.formula ↔ holds σ arrayArray :=
  sourceUIntLiteralPreparation_complete nestedWitness fixture_values.2.1

theorem key_prepared : ∃ r : DeclarationReduction belowKey,
    sourceUIntLiteralPreparation? belowKey = some r ∧ r.formula = .tt ∧
      ∀ σ : State Probe [], holds σ r.formula ↔ holds σ belowKey :=
  sourceUIntLiteralPreparation_complete keyWitness fixture_values.2.2.1

theorem fixed_key_prepared : ∃ r : DeclarationReduction fixedBelowKey,
    sourceUIntLiteralPreparation? fixedBelowKey = some r ∧ r.formula = .tt ∧
      ∀ σ : State Probe [], holds σ r.formula ↔ holds σ fixedBelowKey :=
  sourceUIntLiteralPreparation_complete fixedKeyWitness fixture_values.2.2.2.1

theorem field_prepared : ∃ r : DeclarationReduction belowField,
    sourceUIntLiteralPreparation? belowField = some r ∧ r.formula = .tt ∧
      ∀ σ : State Probe [], holds σ r.formula ↔ holds σ belowField :=
  sourceUIntLiteralPreparation_complete fieldWitness fixture_values.2.2.2.2

/-- The new computed-hit path has kernel validity with the exact old hash-free premise. -/
theorem discovered_validity : Fml.ValidH arrayStruct ∧ Fml.ValidH arrayArray ∧
    Fml.ValidH belowKey ∧ Fml.ValidH fixedBelowKey ∧ Fml.ValidH belowField :=
  ⟨sourceUIntLiteralDiscovery_validH discovered_fixtures.1 (by decide +kernel),
    sourceUIntLiteralDiscovery_validH discovered_fixtures.2.1 (by decide +kernel),
    sourceUIntLiteralDiscovery_validH discovered_fixtures.2.2.1 (by decide +kernel),
    sourceUIntLiteralDiscovery_validH discovered_fixtures.2.2.2.1 (by decide +kernel),
    sourceUIntLiteralDiscovery_validH discovered_fixtures.2.2.2.2 (by decide +kernel)⟩

/-- The same actual three-cell antecedent witnesses nonvacuity. -/
theorem inhabited_original_source : holds inhabitedStructState structAntecedent :=
  struct_antecedent_inhabited

/-- The existing false fixed-array model rules out every discovered candidate. -/
theorem false_fixed_refused : sourceUIntLiteralDiscovery? fixedBad = none :=
  sourceUIntLiteralDiscovery_none_of_invalid fixedBad_notValid

/-- A proved target may be outside this source family: discovery is not an
unknown/complement-of-coverage classification. -/
theorem proved_target_outside_discovery :
    sourceUIntLiteralDiscovery? (.tt : Fml Probe []) = none ∧
    decideGoal (.tt : Fml Probe []) = .proved :=
  ⟨rfl, rfl⟩

/-- A source hit overlaps an already-covered/proved case, distinguishing the
syntactic discovery family from unknown or complement-of-Covered tests. -/
theorem direct_fixed_discovered : (sourceUIntLiteralDiscovery? fixedBlock).isSome = true := by
  decide +kernel

theorem covered_discovery_overlap : fixedBlock.Covered = true ∧
    decideGoal fixedBlock = .proved ∧ (sourceUIntLiteralDiscovery? fixedBlock).isSome = true :=
  ⟨fixedBlock_covered, fixedBlock_proved, direct_fixed_discovered⟩

def unusedSource : Fml Probe [] :=
  .imp (.all (.user "unused") .uint (.imp (sourceUIntBelow (uintOfNat 3))
    (.eq (p := .bool) (.app0 (.lit true)) (.app0 (.lit true)))))
    (.eq (p := .bool) (.app0 (.lit true)) (.app0 (.lit true)))

def unusedWitness2 : SourceUIntLiteralChain (uintOfNat 3) (uintOfNat 2) unusedSource :=
  .leaf ⟨.user "unused", .eq (p := .bool) (.app0 (.lit true)) (.app0 (.lit true)), .bool,
    .app0 (.lit true), .app0 (.lit true), by decide +kernel, rfl, rfl⟩

theorem supplied_unused_instance :
    (sourceUIntLiteralChain? unusedSource (uintOfNat 3) (uintOfNat 2)).isSome = true :=
  sourceUIntLiteralChain_complete unusedWitness2

/-- A successful supplied instance need not occur in the source. -/
theorem absent_instance_value : uintOfNat 2 ∉ sourceUIntDiscoveryValues unusedSource := by
  decide +kernel

/-- Zero is separately declared as a candidate, so the ignored-variable
boundary still has an actual computed hit. -/
theorem unused_discovered :
    ((sourceUIntLiteralDiscovery? unusedSource).map (fun hit => (hit.bound, hit.value))) =
      some (uintOfNat 3, uintOfNat 0) := by
  decide +kernel

theorem preserved_global_controls :
    decideGoal arrayStruct = .unknown ∧ decideGoal arrayArray = .unknown ∧
    decideGoal belowKey = .unknown ∧ decideGoal fixedBelowKey = .unknown ∧
    decideGoal belowField = .unknown := preserved_global_unknowns

end Solidity.Examples.DecisionSourceDiscovery
