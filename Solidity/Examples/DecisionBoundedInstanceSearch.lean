import Solidity.Calculus.DecisionBoundedInstanceSearch
import Solidity.Examples.DecisionBoundedInstance

/-! # Formula-derived literal search controls
Actual source hits retain universal certificates. Zero/oversized bounds and
mismatched consequents remain refusal controls, distinct from invalidity.
-/
namespace Solidity.Examples.DecisionBoundedInstanceSearch
open Solidity.Decide
open Solidity.Examples.DecisionArrayGaps
open Solidity.Examples.DecisionBoundedInstance
set_option Elab.async false

def keyHit : BoundedUIntSourceHit belowKey := (boundedUIntSource? belowKey).get (by decide +kernel)
def fieldHit : BoundedUIntSourceHit belowField := (boundedUIntSource? belowField).get (by decide +kernel)

/-- Actual bound3 candidates find the nonfirst literal1 for these source bodies. -/
theorem selected_literal_controls : keyHit.hit.value = uintOfNat 1 ∧
    fieldHit.hit.value = uintOfNat 1 := by decide +kernel

theorem actual_source_certificates : Fml.Valid belowKey ∧ Fml.Valid belowField :=
  ⟨keyHit.valid, fieldHit.valid⟩

theorem actual_hash_certificates : Fml.ValidH belowKey ∧ Fml.ValidH belowField :=
  ⟨keyHit.validH (by decide +kernel), fieldHit.validH (by decide +kernel)⟩

/-- Generic schema completeness, with the original source-derived estimate. -/
theorem nonfirst_schema_complete : (boundedUIntLiteralSearch? keyPrefix.body).isSome = true :=
  boundedUIntLiteralSearch_complete keyWitness (by decide +kernel)

theorem fixed_source_refusal : (boundedUIntSource? fixedBelowKey).isNone = true := by decide +kernel

theorem optional_search_controls :
    (boundedUIntLiteralSearch? optionalGood).map (·.value) = some (uintOfNat 0) ∧
    (boundedUIntLiteralSearch? optionalBad).isNone = true := by decide +kernel

def zeroBound : LFml Probe := .imp
  (.all 0 .uint (.imp (uintBelow 0 (uintOfNat 0)) .tt)) .tt

def hugeBound : PrimTy.uint.Denote := uintOfNat (2 ^ 256 - 1)
def oversized : LFml Probe := .imp
  (.all 0 .uint (.imp (uintBelow 0 hugeBound) .tt)) .tt

/-- The maximum source bound is rejected before sample-list allocation. -/
theorem boundary_refusals : (boundedUIntLiteralSearch? zeroBound).isNone = true ∧
    (boundedUIntLiteralSearch? oversized).isNone = true := by decide +kernel

/-- Budget refusal is not invalidity: these exact formulas are valid. -/
theorem refused_valid_controls : zeroBound.Valid ∧ oversized.Valid := by
  constructor <;> intro g ν hall <;> trivial

/-- New semantic certificates do not silently change existing decision pins. -/
theorem retained_unknowns : decideGoal belowKey = .unknown ∧
    decideGoal belowField = .unknown ∧ decideGoal fixedBelowKey = .unknown :=
  ⟨belowKey_unknown, belowField_unknown, fixedBelowKey_unknown⟩

end Solidity.Examples.DecisionBoundedInstanceSearch
