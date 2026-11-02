import Solidity.Calculus.DecisionSourceBoundary
import Solidity.Examples.DecisionSourceDiscovery

/-! # Allocation-boundary witnesses
The original five assigned source fixtures obtain coverage without a supplied
allocation flag. Their inhabited antecedent and false fixed-array countermodel
remain unchanged. A fresh-allocation formula is outside this source class;
this is not an assertion about its global coverage or verdict.
-/
namespace Solidity.Examples.DecisionSourceBoundary
open Solidity.Decide Solidity.Examples.DecisionArrayGaps
open Solidity.Examples.DecisionSourceDiscovery (discovered_fixtures)

/-- The allocation boundary is derived for all five original sources. -/
theorem fixtures_noAlloc :
    arrayStruct.hasAllocAll = false ∧ arrayArray.hasAllocAll = false ∧
    belowKey.hasAllocAll = false ∧ fixedBelowKey.hasAllocAll = false ∧
    belowField.hasAllocAll = false :=
  ⟨sourceUIntLiteralDiscovery_noAlloc discovered_fixtures.1,
    sourceUIntLiteralDiscovery_noAlloc discovered_fixtures.2.1,
    sourceUIntLiteralDiscovery_noAlloc discovered_fixtures.2.2.1,
    sourceUIntLiteralDiscovery_noAlloc discovered_fixtures.2.2.2.1,
    sourceUIntLiteralDiscovery_noAlloc discovered_fixtures.2.2.2.2⟩

theorem fixtures_covered : arrayStruct.Covered = true ∧ arrayArray.Covered = true ∧
    belowKey.Covered = true ∧ fixedBelowKey.Covered = true ∧ belowField.Covered = true :=
  ⟨sourceUIntLiteralDiscovery_covered discovered_fixtures.1,
    sourceUIntLiteralDiscovery_covered discovered_fixtures.2.1,
    sourceUIntLiteralDiscovery_covered discovered_fixtures.2.2.1,
    sourceUIntLiteralDiscovery_covered discovered_fixtures.2.2.2.1,
    sourceUIntLiteralDiscovery_covered discovered_fixtures.2.2.2.2⟩

/-- The existing hash-free premise is still discharged separately at each source. -/
theorem fixtures_proved : decideGoal arrayStruct = .proved ∧ decideGoal arrayArray = .proved ∧
    decideGoal belowKey = .proved ∧ decideGoal fixedBelowKey = .proved ∧
    decideGoal belowField = .proved :=
  ⟨sourceUIntLiteralDiscovery_proved discovered_fixtures.1 (by decide +kernel),
    sourceUIntLiteralDiscovery_proved discovered_fixtures.2.1 (by decide +kernel),
    sourceUIntLiteralDiscovery_proved discovered_fixtures.2.2.1 (by decide +kernel),
    sourceUIntLiteralDiscovery_proved discovered_fixtures.2.2.2.1 (by decide +kernel),
    sourceUIntLiteralDiscovery_proved discovered_fixtures.2.2.2.2 (by decide +kernel)⟩

/-- The original positive antecedent actually holds at its constructed heap. -/
theorem original_antecedent_inhabited :
    holds Solidity.Examples.DecisionSourceInstance.inhabitedStructState
      Solidity.Examples.DecisionSourceInstance.structAntecedent :=
  Solidity.Examples.DecisionSourceDiscovery.inhabited_original_source

theorem false_fixed_no_discovery : sourceUIntLiteralDiscovery? fixedBad = none :=
  Solidity.Examples.DecisionSourceDiscovery.false_fixed_refused

theorem fixed_countermodel_preserved : ¬ Fml.Valid fixedBad := fixedBad_notValid

def freshOnly : Fml Probe [] :=
  .allocAll (.user "fresh") (.array (.prim .uint)) .tt

theorem freshOnly_hasAllocation : freshOnly.hasAllocAll = true := rfl

theorem freshOnly_no_discovery : sourceUIntLiteralDiscovery? freshOnly = none := rfl

/-- The genuine syntax witness, not merely the search result, is excluded. -/
theorem freshOnly_not_candidate : ¬ Nonempty (SourceUIntLiteralCandidate freshOnly) := by
  intro h
  obtain ⟨candidate⟩ := h
  have hno : freshOnly.hasAllocAll = false := candidate.witness.noAlloc
  change true = false at hno
  cases hno

end Solidity.Examples.DecisionSourceBoundary
