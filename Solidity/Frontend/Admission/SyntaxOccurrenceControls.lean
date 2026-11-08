import Solidity.Frontend.Admission.SyntaxOccurrenceLaws
import Solidity.Frontend.Admission.ExclusionFeatures
import Solidity.Source.Examples

/-! Inhabited exact-payload/order controls. These are syntax inventories,
not execution-root, semantic reachability or profile witnesses. -/
namespace Solidity.Frontend.Admission.OccurrenceControls
open Solidity.Source

def pairTree (left right : String) : Syn (.list .expr) :=
  .cons (.ident left) (.cons (.ident right) .nil)

def pairInventory (left right : String) : List SyntaxOccurrence :=
  [⟨.list .expr, pairTree left right⟩, ⟨.expr, .ident left⟩,
   ⟨.list .expr, .cons (.ident right) .nil⟩, ⟨.expr, .ident right⟩,
   ⟨.list .expr, .nil⟩]

theorem exact_pair_inventory (left right : String) :
    syntaxOccurrences (pairTree left right) = pairInventory left right := rfl

theorem distinct_payload_order :
    syntaxOccurrences (pairTree "left" "right") = pairInventory "left" "right" :=
  exact_pair_inventory "left" "right"

theorem repeated_payloads_retained :
    syntaxOccurrences (pairTree "same" "same") = pairInventory "same" "same" :=
  exact_pair_inventory "same" "same"

/-- The child may not be silently omitted even though its parent is retained. -/
theorem omitted_child_refused :
    syntaxOccurrences (Syn.some (Syn.ident "seed")) ≠
      ([⟨_, Syn.some (Syn.ident "seed")⟩] : List SyntaxOccurrence) := by
  intro h
  have hl := congrArg List.length h
  change 2 = 1 at hl
  cases hl

/-- info: 'Solidity.Frontend.Admission.OccurrenceControls.exact_pair_inventory' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms exact_pair_inventory
/-- info: 'Solidity.Frontend.Admission.OccurrenceControls.distinct_payload_order' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms distinct_payload_order
/-- info: 'Solidity.Frontend.Admission.OccurrenceControls.repeated_payloads_retained' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms repeated_payloads_retained
/-- info: 'Solidity.Frontend.Admission.OccurrenceControls.omitted_child_refused' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms omitted_child_refused
/-- Regression: reuse the existing inhabited rethrow/mixed-buffer syntax,
without copying its parser or claiming bytes-memory typing/admission. -/
theorem canonical_rethrow_feature_retained :
    rootExclusionFeaturesAt Examples.rethrow = [.canonicalRethrow] ∧
      Examples.rethrow.rejections = [] :=
  ⟨rfl,Examples.rethrow_inProfile⟩

theorem different_buffers_remain_assembly :
    rootExclusionFeaturesAt Examples.notRethrow = [.inlineAssembly] ∧
      Examples.notRethrow.rejections = [.inlineAssembly] :=
  ⟨rfl,Examples.notRethrow_rejected⟩

/-- The existing whole-unit fixtures report their five exclusion IDs, including
flags nested in otherwise ordinary syntax. The sixth case is checked below. -/
theorem inherited_exclusion_features_reported :
    .inlineAssembly ∈ sourceFeaturesWithExclusions Examples.withAssembly ∧
    .storageLayout ∈ sourceFeaturesWithExclusions Examples.withLayout ∧
    .unsignedRightShift ∈ sourceFeaturesWithExclusions Examples.withShr ∧
    .removedUnits ∈ sourceFeaturesWithExclusions Examples.withYears ∧
    .removedGenericSolidity ∈ sourceFeaturesWithExclusions Examples.withGeneric := by
  decide

/-- Malformed modifiers retain both their genuine catalog feature and raw
intrinsic refusal. This is intentionally rejected syntax, not eligibility. -/
theorem malformed_modifier_tag_retained :
    let bad := Syn.modifier "m" .none false none
      (.some (.block (.cons Examples.incStmt .nil)))
    rootExclusionFeaturesAt bad = [.invalidModifierBody] ∧
      (syntaxExclusionUses bad).map Prod.snd = [.invalidModifierBody] ∧
      bad.rejections = [.invalidModifierBody] :=
  ⟨rfl,rfl,Examples.modifierNoPlaceholder_rejected⟩

/-- info: 'Solidity.Frontend.Admission.OccurrenceControls.canonical_rethrow_feature_retained' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms canonical_rethrow_feature_retained
/-- info: 'Solidity.Frontend.Admission.OccurrenceControls.different_buffers_remain_assembly' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms different_buffers_remain_assembly
/-- info: 'Solidity.Frontend.Admission.OccurrenceControls.inherited_exclusion_features_reported' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms inherited_exclusion_features_reported
/-- info: 'Solidity.Frontend.Admission.OccurrenceControls.malformed_modifier_tag_retained' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms malformed_modifier_tag_retained

end Solidity.Frontend.Admission.OccurrenceControls
