import Solidity.Calculus.DecisionResidue
import Solidity.Examples.DecisionHaltingOrGaps
import Solidity.Examples.DecisionMappingFieldReason
import Solidity.Examples.DecisionNormalizationResidue
import Solidity.Examples.DecisionHashCore
import Solidity.Examples.DecisionQuantLedger
import Solidity.Examples.DecisionArrayCore
import Solidity.Examples.DecisionArrayGaps
import Solidity.Examples.DecisionGapCensus
import Solidity.Examples.DecisionGaps

/-!
# The residue's fixtures and `DecisionTheorem'`'s witness controls (M7-next)

`Fml.Residue` (`Calculus/DecisionResidue.lean`) is exact by construction, so
`DecisionTheorem'`'s totality off it holds by definition and is not a
completeness result. These fixtures show what the statement does carry:

* **Residue members** (in target, every route refuses): on leaves without a
  hash, a halting `||` guard in an APF block, valid (`floorClaim 1`) and false
  (`floorBad`), with no VA1 label; leaves carrying VA1's mapping-bearing
  reversed-field label (`mappingReversed`, every leaf route's refusal listed)
  and normalization-budget labels (`exhausted`); a leaf in no labelled class
  (`sibling`). On a leaf with a hash, every hash try refusing (`hashBudget`).
* **Witness controls**: the theorem's hypotheses are jointly satisfiable, by
  in-target, non-residue leaves from the feature fixtures of earlier
  milestones (quantified arithmetic, APF blocks, storage and fixed arrays,
  ledger reads and blocks, memory, KeY `int`, quantified ledger, hashes), each
  answer certified by `DecisionTheorem'`. Which route answers each is not
  pinned here.
* **Negative controls**: a residue leaf is not claimed; a valid one and a
  false one sit in the residue alike, and the theorem's conclusion fails there.

Membership comes from the existing kernel-checked `unknown` pins through
`residue_iff_unknown` where one exists (`floorClaim 1`, `floorBad`,
`mappingReversed`), and from `decide +kernel` on `Fml.Residue` otherwise.
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

/-- Every leaf route refuses it, each refusal named, in `decideGoal`'s order. -/
theorem mapping_routeRefusals : mappingReversed.routeRefusals = leafRoutes := by decide +kernel

/-- Its finer VA1 source reason is reported (the source reasons consult no route). -/
theorem mapping_sourceReason : mappingReversed.sourceReasons =
    [ResidueReason.mappingReversedFreshFieldReason] := by decide +kernel

end Mapping

section Budget
open Solidity.Examples.DecisionNormalizationResidue

/-- VA1's normalization budget (2049 visits against 2048): in the residue. -/
theorem exhausted_residue : exhausted.inTarget {} = true ∧ exhausted.Residue :=
  ⟨target_controls.1, by decide +kernel⟩

/-- Its finer VA1 source reasons (two-binder and primitive-prefix budget). -/
theorem exhausted_sourceReasons : exhausted.sourceReasons =
    [ResidueReason.twoUIntPrefixOverNormalizationBudgetReason,
      ResidueReason.primitivePrefixNormalizationReason] := by decide +kernel

/-- A source reason is not a residue test: the 1025-visit sibling has no
budget reason and still sits in the residue, and the class consults no route. -/
theorem sibling_residue_without_reason : sibling.Residue ∧ sibling.sourceReasons = [] :=
  ⟨by decide +kernel, by decide +kernel⟩

end Budget


section Hash
open Solidity.Examples.DecisionHashes
open Solidity.Examples.Tactics.Hashing (Names)

/-- `x + y == 5`, under two `uint` binders inside the two fresh strings. -/
def hashAtom : Fml Names [.val .uint, .val .uint, .mem Str, .mem Str] :=
  .eq (.app2 (.binop .add rfl) (.pvV .here) (.pvV (.there .here))) (num 5)

/-- `n` doublings of a conjunction. -/
def doubled {Γ : Ctx} (atom : Fml Names Γ) : Nat → Fml Names Γ
  | 0 => atom
  | n + 1 => .and (doubled atom n) (doubled atom n)

/-- **`∀ fresh s t. keccak256(s) != keccak256(t) → ∀ x y. (x + y == 5) ∧ …`**
(1024 copies of the atom, as `exhausted`'s body under the two strings): hashes
compared against their kind, so in target. Built from constructors, as
`DecisionHashes` builds its leaves: `dl!` has no fresh-string notation. -/
def hashBudget : Fml Names [] :=
  strings (.imp (.not (.eq hS hT))
    (.all (.user "x") .uint (.all (.user "y") .uint (doubled hashAtom 10))))

/-- In target, with a hash, and every hash try answers `unknown` (`Fml.Residue`
on a leaf with a hash). Why each try refuses is not shown here. -/
theorem hashBudget_residue : hashBudget.inTarget {} = true ∧ hashBudget.hasHash = true ∧
    hashBudget.Residue := by decide +kernel

end Hash

/-! ## Witness controls: the hypotheses are jointly satisfiable

In-target, non-residue leaves from earlier milestones' feature fixtures, each
answer certified by `DecisionTheorem'` (not merely evaluated). The route that
answers is not pinned. -/

section Witnesses

/-- `∀ uint` prefixes over linear arithmetic: proved and refuted. -/
theorem dependent_witnesses :
    Answered DecisionNormalizationResidue.reflexive ∧ Answered DecisionNormalizationResidue.small :=
  ⟨DecisionTheorem' {} _ _ DecisionNormalizationResidue.nonresidual_targets.2.1
      (not_residue_of_ne (by rw [DecisionNormalizationResidue.reflexive_proved]; exact nofun)),
    DecisionTheorem' {} _ _ DecisionNormalizationResidue.nonresidual_targets.1
      (not_residue_of_ne (by rw [DecisionNormalizationResidue.small_decision_refuted]; exact nofun))⟩

/-- A `bool`-quantified APF fixture. -/
theorem quant_witness : Answered DecisionHaltingOrGaps.guarded :=
  DecisionTheorem' {} _ _ (by decide +kernel)
    (not_residue_of_ne (by rw [DecisionHaltingOrGaps.guarded_proved]; exact nofun))

/-- A block over a storage array (feature 32's fixture). -/
theorem arrayBlock_witness : Answered Decision.gapArrayBlock :=
  DecisionTheorem' {} _ _ Decision.gapArrayBlock_inTarget
    (not_residue_of_ne Decision.gapArrayBlock_answers)

/-- Bounded fixed-array instances: proved and refuted. -/
theorem fixedArray_witnesses : Answered DecisionArrayGaps.fixedBlock ∧
    Answered DecisionArrayGaps.fixedBad :=
  ⟨DecisionTheorem' {} _ _ DecisionArrayGaps.fixedBlock_target
      (not_residue_of_ne (by rw [DecisionArrayGaps.fixedBlock_proved]; exact nofun)),
    DecisionTheorem' {} _ _ DecisionArrayGaps.fixedBad_target
      (not_residue_of_ne (by
        obtain ⟨σ, h, _⟩ := DecisionArrayGaps.fixedBad_refuted
        rw [h]; exact nofun))⟩

/-- Memory: a given-heap parameter (proved) and a reversed fresh struct field
(refuted at its exact child-heap state). -/
theorem memory_witnesses : Answered Decision.memParamSame ∧ Answered Decision.memStructReversed :=
  ⟨DecisionTheorem' {} _ _ DecisionGapCensus.hiddenParameter_target
      (not_residue_of_ne (by rw [DecisionGapCensus.hiddenParameter_proved]; exact nofun)),
    DecisionTheorem' {} _ _ DecisionGapCensus.reversedStruct_target
      (not_residue_of_ne (by rw [DecisionGapCensus.reversedStruct_exact_state]; exact nofun))⟩

/-- KeY `int` binders with two anchors (feature 30/31's fixture). -/
theorem kenc_witness : Answered DecisionKInt.gapKIntTwoAnchors :=
  DecisionTheorem' {} _ _ DecisionKInt.gapKIntTwoAnchors_inTarget
    (not_residue_of_ne (by rw [DecisionKInt.gapKIntTwoAnchors_goal_verdict]; exact nofun))

/-- A quantified ledger leaf (feature 33's fixture). -/
theorem quantLedger_witness : Answered DecisionKInt.gapQuantLedger :=
  DecisionTheorem' {} _ _ DecisionKInt.gapQuantLedger_inTarget
    (not_residue_of_ne (decideGoal_complete DecisionQuantLedger.original_covered (by decide +kernel)))

/-- A leaf with hashes of one kind. -/
theorem hash_witness : Answered DecisionHashes.namesSet :=
  DecisionTheorem' {} _ _ (by decide +kernel) (not_residue_of_ne DecisionHashes.namesSet_answers)

/-- A positive KeY `int` binder (feature 26's fixture). -/
theorem kint_witness : Answered Decision.gapKIntBinder :=
  DecisionTheorem' {} _ _ Decision.gapKIntBinder_inTarget
    (not_residue_of_ne Decision.gapKIntBinder_answers)

/-- A write to the starting ledger (feature 9's fixture). -/
theorem ledger_witness : Answered Decision.gapLedgerWrite :=
  DecisionTheorem' {} _ _ Decision.gapLedgerWrite_inTarget
    (not_residue_of_ne Decision.gapLedgerWrite_answers)

/-- A block over the ledger (feature 21's fixture). -/
theorem ledgerBlock_witness : Answered Decision.gapLedgerBlock :=
  DecisionTheorem' {} _ _ Decision.gapLedgerBlock_inTarget
    (not_residue_of_ne (decideGoal_complete Decision.gapLedgerBlock_covered rfl))

/-- A storage array column read at a symbolic index (feature 10's fixture). -/
theorem storageArray_witness : Answered Decision.gapColumn :=
  DecisionTheorem' {} _ _ Decision.gapColumn_inTarget
    (not_residue_of_ne Decision.gapColumn_answers)

end Witnesses

/-! ## Negative controls: a residue leaf is not claimed -/

/-- A valid leaf and a false leaf of one shape are both in target and in the
residue; the theorem's conclusion fails at each, so it claims neither. -/
theorem residue_not_claimed :
    Fml.Valid (DecisionHaltingOrGaps.floorClaim 1) ∧ ¬ Fml.Valid DecisionHaltingOrGaps.floorBad ∧
      ¬ Answered (DecisionHaltingOrGaps.floorClaim 1) ∧
      ¬ Answered DecisionHaltingOrGaps.floorBad :=
  ⟨DecisionHaltingOrGaps.floorClaim_one_valid, DecisionHaltingOrGaps.floorBad_notValid,
    not_answered_of_residue floorValid_residue.2, not_answered_of_residue floorBad_residue.2⟩

/-- info: 'Solidity.Examples.DecisionResidue.dependent_witnesses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms dependent_witnesses

/-- info: 'Solidity.Examples.DecisionResidue.quant_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms quant_witness

/-- info: 'Solidity.Examples.DecisionResidue.arrayBlock_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms arrayBlock_witness

/-- info: 'Solidity.Examples.DecisionResidue.fixedArray_witnesses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fixedArray_witnesses

/-- info: 'Solidity.Examples.DecisionResidue.memory_witnesses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms memory_witnesses

/-- info: 'Solidity.Examples.DecisionResidue.kenc_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms kenc_witness

/-- info: 'Solidity.Examples.DecisionResidue.quantLedger_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms quantLedger_witness

/-- info: 'Solidity.Examples.DecisionResidue.hash_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hash_witness

/-- info: 'Solidity.Examples.DecisionResidue.kint_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms kint_witness

/-- info: 'Solidity.Examples.DecisionResidue.ledger_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ledger_witness

/-- info: 'Solidity.Examples.DecisionResidue.ledgerBlock_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ledgerBlock_witness

/-- info: 'Solidity.Examples.DecisionResidue.storageArray_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms storageArray_witness

/-- info: 'Solidity.Examples.DecisionResidue.residue_not_claimed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms residue_not_claimed

/-- info: 'Solidity.Examples.DecisionResidue.floorValid_residue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms floorValid_residue

/-- info: 'Solidity.Examples.DecisionResidue.floorBad_residue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms floorBad_residue

/-- info: 'Solidity.Examples.DecisionResidue.mapping_residue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mapping_residue

/-- info: 'Solidity.Examples.DecisionResidue.mapping_routeRefusals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mapping_routeRefusals

/-- info: 'Solidity.Examples.DecisionResidue.exhausted_residue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms exhausted_residue

/--
info: 'Solidity.Examples.DecisionResidue.sibling_residue_without_reason' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms sibling_residue_without_reason

/-- info: 'Solidity.Examples.DecisionResidue.hashBudget_residue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hashBudget_residue

end Solidity.Examples.DecisionResidue
