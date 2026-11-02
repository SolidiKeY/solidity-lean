import Solidity.Calculus.DecisionBoundedInstanceSource
import Solidity.Examples.DecisionArrayGaps

/-! # Actual keyed/field source clients and partial-read controls
Recognition refusal is distinct from invalidity or a global unknown verdict.
The real existing source/prefix certificates are computed, not assumed.
-/
namespace Solidity.Examples.DecisionBoundedInstance
open Solidity.Decide
open Solidity.Examples.DecisionArrayGaps
set_option Elab.async false

def keySource : SourceReduction belowKey := (sourceReduction? belowKey).get (by decide +kernel)
def keyPrefix : UniversalPrefix keySource.leaf.elim.condSimp.prenex :=
  (UniversalPrefix.ofFormula? 1024 keySource.leaf.elim.condSimp.prenex).get (by decide +kernel)
def keyWitness : BoundedUIntLiteralInstance keyPrefix.body (uintOfNat 1) :=
  (boundedUIntLiteralInstance? keyPrefix.body (uintOfNat 1)).get (by decide +kernel)

def fieldSource : SourceReduction belowField := (sourceReduction? belowField).get (by decide +kernel)
def fieldPrefix : UniversalPrefix fieldSource.leaf.elim.condSimp.prenex :=
  (UniversalPrefix.ofFormula? 1024 fieldSource.leaf.elim.condSimp.prenex).get (by decide +kernel)
def fieldWitness : BoundedUIntLiteralInstance fieldPrefix.body (uintOfNat 1) :=
  (boundedUIntLiteralInstance? fieldPrefix.body (uintOfNat 1)).get (by decide +kernel)

/-- The certificates consume actual pipeline outputs, including the key prefix. -/
theorem actual_source_validity : Fml.Valid belowKey ∧ Fml.Valid belowField :=
  ⟨boundedUIntInstance_source_valid keySource keyPrefix keyWitness,
    boundedUIntInstance_source_valid fieldSource fieldPrefix fieldWitness⟩

theorem actual_hash_certificates : Fml.ValidH belowKey ∧ Fml.ValidH belowField :=
  ⟨boundedUIntInstance_source_validH keySource keyPrefix keyWitness (by decide +kernel),
    boundedUIntInstance_source_validH fieldSource fieldPrefix fieldWitness (by decide +kernel)⟩

/-- Both original source witnesses now receive coverage and certified positive verdicts. -/
theorem source_route_controls : belowKey.Covered = true ∧ belowField.Covered = true ∧
    decideGoal belowKey = .proved ∧ decideGoal belowField = .proved :=
  ⟨belowKey_covered, belowField_covered, belowKey_proved, belowField_proved⟩

def fixedSource : SourceReduction fixedBelowKey :=
  (sourceReduction? fixedBelowKey).get (by decide +kernel)
def fixedPrefix : UniversalPrefix fixedSource.leaf.elim.condSimp.prenex :=
  (UniversalPrefix.ofFormula? 1024 fixedSource.leaf.elim.condSimp.prenex).get (by decide +kernel)

/-- The actual fixed-below-key source is outside this exact instance syntax. -/
theorem fixed_source_refusal : fixedPrefix.body.boundedUIntLiteralInstance (uintOfNat 1) = false := by
  decide +kernel

theorem fixed_source_route : fixedBelowKey.Covered = true ∧ decideGoal fixedBelowKey = .proved :=
  ⟨fixedBelowKey_covered, fixedBelowKey_proved⟩

def partialBody : LFml Probe := .eq (.err (s := .val .uint)) (.err (s := .val .uint))
def partialGood : LFml Probe := .imp
  (.all 0 .uint (.imp (uintBelow 0 (uintOfNat 3)) partialBody)) partialBody
def partialBad : LFml Probe := .imp
  (.all 0 .uint (.imp (uintBelow 0 (uintOfNat 3)) partialBody))
  (.eq (.err (s := .val .uint)) (.app0 (.lit (uintOfNat 0))))

theorem partial_recognition_controls : partialGood.boundedUIntLiteralInstance (uintOfNat 1) = true ∧
    partialGood.boundedUIntLiteralInstance (uintOfNat 3) = false ∧
    partialBad.boundedUIntLiteralInstance (uintOfNat 1) = false := by decide +kernel

def partialWitness : BoundedUIntLiteralInstance partialGood (uintOfNat 1) :=
  (boundedUIntLiteralInstance? partialGood (uintOfNat 1)).get (by decide +kernel)

theorem partial_valid : partialGood.Valid := partialWitness.valid

/-- Strict LFml.eq requires returned operands; this exact old test body is false. -/
theorem strict_partial_antecedent_refuted :
    ¬ (LFml.all 0 .uint (.imp (uintBelow 0 (uintOfNat 3)) partialBody)).holds
      (State.init Probe) AEnv.dflt := by
  intro h
  exact h (uintOfNat 0) (by rfl)

/-- The old strict mismatched fixture is valid vacuously, so refusal alone is
not a countermodel claim. Its definition remains unchanged. -/
theorem strict_mismatch_valid : partialBad.Valid := by
  intro g ν hall
  exact False.elim (hall (uintOfNat 0) (by rfl))

def optionalBody : LFml Probe := LFml.optEq (.err (s := .val .uint)) (.err (s := .val .uint))
def optionalGood : LFml Probe := .imp
  (.all 0 .uint (.imp (uintBelow 0 (uintOfNat 3)) optionalBody)) optionalBody
def optionalBad : LFml Probe := .imp
  (.all 0 .uint (.imp (uintBelow 0 (uintOfNat 3)) optionalBody))
  (LFml.optEq (.err (s := .val .uint)) (.app0 (.lit (uintOfNat 0))))

theorem optional_recognition_controls : optionalGood.boundedUIntLiteralInstance (uintOfNat 1) = true ∧
    optionalGood.boundedUIntLiteralInstance (uintOfNat 3) = false ∧
    optionalBad.boundedUIntLiteralInstance (uintOfNat 1) = false := by decide +kernel

def optionalWitness : BoundedUIntLiteralInstance optionalGood (uintOfNat 1) :=
  (boundedUIntLiteralInstance? optionalGood (uintOfNat 1)).get (by decide +kernel)

theorem optional_valid : optionalGood.Valid := optionalWitness.valid

/-- Existing optEq semantics makes two failed readings equal; the antecedent
is inhabited without changing the strict equality operation. -/
theorem optional_antecedent_inhabited :
    (LFml.all 0 .uint (.imp (uintBelow 0 (uintOfNat 3)) optionalBody)).holds
      (State.init Probe) AEnv.dflt := by
  intro value hguard
  exact (LFml.optEq_holds _ _ _ _).mpr rfl

/-- The mismatched optional result is an actual countermodel, at this same state. -/
theorem mismatched_countermodel : ¬ optionalBad.holds (State.init Probe) AEnv.dflt := by
  intro h
  have hn : (LFml.optEq (.err (s := .val .uint)) (.app0 (.lit (uintOfNat 0))) : LFml Probe).holds
      (State.init Probe) AEnv.dflt := h optional_antecedent_inhabited
  have he : (none : Option PrimTy.uint.Denote) = some (uintOfNat 0) :=
    (LFml.optEq_holds _ _ _ _).mp hn
  cases he

def quantifiedBody : LFml Probe := .all 1 .uint .tt
def quantifiedGood : LFml Probe := .imp
  (.all 0 .uint (.imp (uintBelow 0 (uintOfNat 3)) quantifiedBody)) quantifiedBody

/-- Unsupported quantified bodies can be valid; refusal is not invalidity. -/
theorem quantified_body_refusal : quantifiedGood.boundedUIntLiteralInstance (uintOfNat 1) = false := by
  decide +kernel

theorem quantified_body_valid : quantifiedGood.Valid := by
  intro g ν hall value
  trivial

theorem constructive_family_controls :
    decide (Nonempty (BoundedUIntLiteralInstance partialGood (uintOfNat 1))) = true ∧
    decide (Nonempty (BoundedUIntLiteralInstance partialGood (uintOfNat 3))) = false := by
  decide +kernel

end Solidity.Examples.DecisionBoundedInstance
