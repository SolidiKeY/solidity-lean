import Solidity.Calculus.DecisionResidue
import Solidity.Examples.DecisionHaltingOrGaps
import Solidity.Examples.DecisionMappingFieldReason
import Solidity.Examples.DecisionNormalizationResidue
import Solidity.Examples.DecisionHashCore
import Solidity.Examples.DecisionQuantLedger
import Solidity.Examples.DecisionArrayCore
import Solidity.Examples.DecisionArrayGaps
import Solidity.Examples.DecisionGapCensus

/-!
# The residue's fixtures and `DecisionTheorem'`'s witness controls (M7-next)

`Fml.Residue` (`Calculus/DecisionResidue.lean`) is exact by construction, so
`DecisionTheorem'`'s totality off it holds by definition and is not a
completeness result. These fixtures show what the statement does carry:

* **Residue members, one per named reason** (in target, every route refuses):
  a halting `||` guard in an APF block, valid (`floorClaim 1`) and false
  (`floorBad`); VA1's mapping-bearing reversed field (`mappingReversed`); VA1's
  normalization budget (`exhausted`); every hash try refusing (`hashBudget`).
* **Witness controls**: the theorem's hypotheses are jointly satisfiable, by
  an in-target, non-residue leaf of each route family, each with its answer
  certified by `DecisionTheorem'`.
* **Negative controls**: a residue leaf is not claimed; a valid one and a
  false one sit in the residue alike, and the theorem's conclusion fails there.

Residue membership is derived from the existing kernel-checked `unknown` pins
through `residue_iff_unknown`; nothing is evaluated twice.
-/

namespace Solidity.Examples.DecisionResidue

open Solidity.Decide
set_option Elab.async false

/-- The theorem's conclusion, named for the controls. -/
def Answered {C : Contract} (φ : Fml C []) : Prop :=
  (decideGoal φ = .proved ∧ Fml.ValidH φ) ∨
    (∃ σ : State C [], decideGoal φ = .refuted σ ∧ ¬ Fml.holdsH σ φ)

theorem not_residue_of_ne {C : Contract} {φ : Fml C []} (h : decideGoal φ ≠ .unknown) :
    ¬ φ.Residue := fun hr => h (residue_iff_unknown.1 hr)

theorem not_answered_of_residue {C : Contract} {φ : Fml C []} (h : φ.Residue) :
    ¬ Answered φ := by
  have hu := residue_iff_unknown.1 h
  rintro (⟨hp, _⟩ | ⟨σ, hs, _⟩)
  · rw [hu] at hp; cases hp
  · rw [hu] at hs; cases hs

/-! ## Residue members, one per named reason -/

section Members
open Solidity.Examples.DecisionHaltingOrGaps

/-- Halting `||` guard, valid leaf: in target, in the residue. -/
theorem floorValid_residue : (floorClaim 1).inTarget {} = true ∧ (floorClaim 1).Residue :=
  ⟨validAPF_target, residue_iff_unknown.2 validAPF_unknown⟩

/-- Halting `||` guard, false leaf: in target, in the residue. -/
theorem floorBad_residue : floorBad.inTarget {} = true ∧ floorBad.Residue :=
  ⟨falseAPF_target, residue_iff_unknown.2 falseAPF_unknown⟩

end Members

section Mapping
open Solidity.Examples.DecisionResidueReasons

/-- VA1's mapping-bearing reversed field: in target, in the residue. -/
theorem mapping_residue : mappingReversed.inTarget {} = true ∧ mappingReversed.Residue :=
  ⟨mapping_target_control, residue_iff_unknown.2 mapping_global_unknown⟩

/-- Its finer VA1 source reason is reported (the source reasons consult no route). -/
theorem mapping_sourceReason : mappingReversed.sourceReasons =
    [ResidueReason.mappingReversedFreshFieldReason] := by decide +kernel

end Mapping

section Budget
open Solidity.Examples.DecisionNormalizationResidue

/-- VA1's normalization budget (2049 visits against 2048): in the residue. -/
theorem exhausted_residue : exhausted.inTarget {} = true ∧ exhausted.Residue :=
  ⟨target_controls.1, residue_iff_unknown.2 (by rfl)⟩

/-- Its finer VA1 source reasons (two-binder and primitive-prefix budget). -/
theorem exhausted_sourceReasons : exhausted.sourceReasons =
    [ResidueReason.twoUIntPrefixOverNormalizationBudgetReason,
      ResidueReason.primitivePrefixNormalizationReason] := by decide +kernel

/-- A source reason is not a residue test: the 1025-visit sibling has no
budget reason and still sits in the residue, and the class consults no route. -/
theorem sibling_residue_without_reason : sibling.Residue ∧ sibling.sourceReasons = [] :=
  ⟨residue_iff_unknown.2 (by rfl), by decide +kernel⟩

end Budget

/-! ## Witness controls: the hypotheses are jointly satisfiable

An in-target, non-residue leaf of each route family, its answer certified by
`DecisionTheorem'` (not merely evaluated). -/

section Witnesses

/-- Quantifier-free arithmetic (`dependentReduction?`): proved and refuted. -/
theorem dependent_witnesses :
    Answered DecisionNormalizationResidue.reflexive ∧ Answered DecisionNormalizationResidue.small :=
  ⟨DecisionTheorem' {} _ _ DecisionNormalizationResidue.nonresidual_targets.2.1
      (not_residue_of_ne (by rw [DecisionNormalizationResidue.reflexive_proved]; exact nofun)),
    DecisionTheorem' {} _ _ DecisionNormalizationResidue.nonresidual_targets.1
      (not_residue_of_ne (by rw [DecisionNormalizationResidue.small_decision_refuted]; exact nofun))⟩

/-- A Boolean-guarded APF block (`quantReduction?`). -/
theorem quant_witness : Answered DecisionHaltingOrGaps.guarded :=
  DecisionTheorem' {} _ _ (by decide +kernel)
    (not_residue_of_ne (by rw [DecisionHaltingOrGaps.guarded_proved]; exact nofun))

/-- Blocks over storage arrays (`arrayBlockReduction?`). -/
theorem arrayBlock_witness : Answered Decision.gapArrayBlock :=
  DecisionTheorem' {} _ _ Decision.gapArrayBlock_inTarget
    (not_residue_of_ne Decision.gapArrayBlock_answers)

/-- Bounded fixed-array instances (the array-block route): proved and refuted. -/
theorem fixedArray_witnesses : Answered DecisionArrayGaps.fixedBlock ∧
    Answered DecisionArrayGaps.fixedBad :=
  ⟨DecisionTheorem' {} _ _ DecisionArrayGaps.fixedBlock_target
      (not_residue_of_ne (by rw [DecisionArrayGaps.fixedBlock_proved]; exact nofun)),
    DecisionTheorem' {} _ _ DecisionArrayGaps.fixedBad_target
      (not_residue_of_ne (by
        obtain ⟨σ, h, _⟩ := DecisionArrayGaps.fixedBad_refuted
        rw [h]; exact nofun))⟩

/-- The memory route: a given-heap parameter (proved) and a reversed fresh
struct field (refuted at its exact child-heap state). -/
theorem memory_witnesses : Answered Decision.memParamSame ∧ Answered Decision.memStructReversed :=
  ⟨DecisionTheorem' {} _ _ DecisionGapCensus.hiddenParameter_target
      (not_residue_of_ne (by rw [DecisionGapCensus.hiddenParameter_proved]; exact nofun)),
    DecisionTheorem' {} _ _ DecisionGapCensus.reversedStruct_target
      (not_residue_of_ne (by rw [DecisionGapCensus.reversedStruct_exact_state]; exact nofun))⟩

/-- KeY `int` binders over two words (`decideKEnc`). -/
theorem kenc_witness : Answered DecisionKInt.gapKIntTwoAnchors :=
  DecisionTheorem' {} _ _ DecisionKInt.gapKIntTwoAnchors_inTarget
    (not_residue_of_ne (by rw [DecisionKInt.gapKIntTwoAnchors_goal_verdict]; exact nofun))

/-- Quantified ledger leaves (`decideQuantLedger`, feature 33). -/
theorem quantLedger_witness : Answered DecisionKInt.gapQuantLedger :=
  DecisionTheorem' {} _ _ DecisionKInt.gapQuantLedger_inTarget
    (not_residue_of_ne (decideGoal_complete DecisionQuantLedger.original_covered (by decide +kernel)))

/-- A leaf with hashes (`decideHash`, one kind). -/
theorem hash_witness : Answered DecisionHashes.namesSet :=
  DecisionTheorem' {} _ _ (by decide +kernel) (not_residue_of_ne DecisionHashes.namesSet_answers)

end Witnesses

/-! ## Negative controls: a residue leaf is not claimed -/

/-- A valid leaf and a false leaf of one shape are both in target and in the
residue; the theorem's conclusion fails at each, so it claims neither. -/
theorem residue_not_claimed :
    Fml.Valid (DecisionHaltingOrGaps.floorClaim 1) ∧
      ¬ Answered (DecisionHaltingOrGaps.floorClaim 1) ∧
      ¬ Answered DecisionHaltingOrGaps.floorBad :=
  ⟨DecisionHaltingOrGaps.floorClaim_one_valid, not_answered_of_residue floorValid_residue.2,
    not_answered_of_residue floorBad_residue.2⟩

#print axioms dependent_witnesses
#print axioms quant_witness
#print axioms arrayBlock_witness
#print axioms fixedArray_witnesses
#print axioms memory_witnesses
#print axioms kenc_witness
#print axioms quantLedger_witness
#print axioms hash_witness
#print axioms residue_not_claimed
#print axioms mapping_residue
#print axioms exhausted_residue

end Solidity.Examples.DecisionResidue
