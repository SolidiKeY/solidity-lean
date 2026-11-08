import Solidity.Frontend.Admission.SyntaxOccurrenceLaws
import Solidity.Frontend.Admission.ExclusionFeatures
import Solidity.Source.Examples

/-! Inhabited exact-payload/order controls. These are syntax inventories, not execution-root, semantic reachability or profile witnesses. -/
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
/-- Regression: reuse the existing inhabited rethrow/mixed-buffer syntax, without copying its parser or claiming bytes-memory typing/admission. -/
theorem canonical_rethrow_feature_retained :
    rootExclusionFeaturesAt Examples.rethrow = [.canonicalRethrow] ∧
      Examples.rethrow.rejections = [] :=
  ⟨rfl,Examples.rethrow_inProfile⟩

theorem different_buffers_remain_assembly :
    rootExclusionFeaturesAt Examples.notRethrow = [.inlineAssembly] ∧
      Examples.notRethrow.rejections = [.inlineAssembly] :=
  ⟨rfl,Examples.notRethrow_rejected⟩

/-- The existing whole-unit fixtures report their five exclusion IDs, including flags nested in otherwise ordinary syntax. The sixth case is checked below. -/
theorem inherited_exclusion_features_reported :
    .inlineAssembly ∈ sourceFeaturesWithExclusions Examples.withAssembly ∧
    .storageLayout ∈ sourceFeaturesWithExclusions Examples.withLayout ∧
    .unsignedRightShift ∈ sourceFeaturesWithExclusions Examples.withShr ∧
    .removedUnits ∈ sourceFeaturesWithExclusions Examples.withYears ∧
    .removedGenericSolidity ∈ sourceFeaturesWithExclusions Examples.withGeneric := by
  decide

/-- Malformed modifiers retain both their genuine catalog feature and raw intrinsic refusal. This is intentionally rejected syntax, not eligibility. -/
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


open Solidity.Language

theorem original_header_refusal (path : String) :
    sourceSubsetRefusals (structuralImportUnit path) (fun f => decide (f ≠ .imports)) =
      [(⟨_,Syn.importPath path none⟩,.imports)] ∧
    sourceSubsetRefusal? (Syn.unit Syn.nil) (fun f => decide (f ≠ .imports)) = none ∧
    (structuralImportUnit path).env = (Syn.unit Syn.nil).env := ⟨rfl,rfl,rfl⟩

theorem literal_refusal_site (literal : Lit) :
    syntaxFieldRefusal? (Syn.lit literal) syntaxSubsetFeaturesAt (fun _ => false) =
      some (⟨_,Syn.lit literal⟩,literalFeature literal) := by
  cases literal <;> rfl

/-- Intentional negative control: an empty classifier silences diagnostics on genuinely refused syntax. -/
theorem silent_empty_classifier_is_not_raw_safety :
    syntaxFieldRefusal? Examples.withAssembly (fun _ => ([] : List Feature)) (fun _ => false) = none ∧
      .inlineAssembly ∈ Examples.withAssembly.rejections :=
  ⟨emptySyntaxClassifier_none _ _,by decide⟩

/-- info: 'Solidity.Frontend.Admission.OccurrenceControls.original_header_refusal' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms original_header_refusal
/-- info: 'Solidity.Frontend.Admission.OccurrenceControls.literal_refusal_site' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms literal_refusal_site
/-- info: 'Solidity.Frontend.Admission.OccurrenceControls.silent_empty_classifier_is_not_raw_safety' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms silent_empty_classifier_is_not_raw_safety


theorem removed_years_payload_refused (n : NumLit) :
    syntaxFieldRefusal? (Syn.litUnit n .years) payloadFeaturesAt
      (fun f => decide (f ≠ .removedUnits)) = some (⟨_,Syn.litUnit n .years⟩,.removedUnits) ∧
    (Syn.litUnit n .years).rejections = [.removedUnits] := ⟨rfl,rfl⟩

theorem nested_prefix_payloads :
    (syntaxPayloadUses (Syn.unaryPrefix .inc (Syn.unaryPrefix .delete (.ident "x")))).map Prod.snd =
      [.increments,.deleteExpression] := rfl

/-- info: 'Solidity.Frontend.Admission.OccurrenceControls.removed_years_payload_refused' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms removed_years_payload_refused
/-- info: 'Solidity.Frontend.Admission.OccurrenceControls.nested_prefix_payloads' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms nested_prefix_payloads


/-! Regression: metadata visibility must survive unused-declaration traversal; absent fields must not acquire defaults, and function-type payloads must not be treated as legality evidence. -/
def explicitVisibilityUnit (vis : Option Visibility) : Syn .unit :=
  .unit (.cons (.topPart (.function (.ident "unused") .nil vis none .nil false none .nil .none)) .nil)

theorem explicit_visibility_unused (vis : Option Visibility) :
    (declarationVisibilityUses (explicitVisibilityUnit vis).env).map Prod.snd = vis.toList ∧
    (syntaxVisibilityUses (explicitVisibilityUnit vis)).map Prod.snd = vis.toList := by
  cases vis <;> exact ⟨rfl,rfl⟩

theorem visibility_carriers (v : Visibility) (cv : CtorVis) (sv : StateVis) :
    [visibilityFieldsAt (Syn.constructor .nil .nil false (some cv) (.block .nil)),
     visibilityFieldsAt (Syn.function (t := true) (.ident "f") .nil (some v) none .nil false none .nil .none),
     visibilityFieldsAt (Syn.fallback .fbNoParams true none .nil false none .none),
     visibilityFieldsAt (Syn.receive true false .nil false none .none),
     visibilityFieldsAt (Syn.stateVar (.elem .bool) (some sv) none none false "x" .none),
     visibilityFieldsAt (Syn.fnType .nil (some v) none .nil)] =
      [[ctorVisibility cv],[v],[.external],[.external],[stateVisibility sv],[v]] := rfl

/-- info: 'Solidity.Frontend.Admission.OccurrenceControls.explicit_visibility_unused' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms explicit_visibility_unused
/-- info: 'Solidity.Frontend.Admission.OccurrenceControls.visibility_carriers' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms visibility_carriers

end Solidity.Frontend.Admission.OccurrenceControls
