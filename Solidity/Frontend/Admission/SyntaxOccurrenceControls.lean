import Solidity.Frontend.Admission.SyntaxOccurrenceLaws
import Solidity.Frontend.Admission.ExclusionFeatures
import Solidity.Source.Examples

/-! Inhabited exact-payload/order controls. These are syntax inventories, not execution-root, semantic reachability or profile witnesses. Qualifier controls guard omitted override keywords and transient flags without asserting legality. -/
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


/-! Regression: written mutability survives unused declaration traversal, while getter inference must not create raw written qualifiers. These are syntax inventories, not effect/admission witnesses. -/
def explicitMutabilityUnit (state : Option Mutability) : Syn .unit :=
  .unit (.cons (.topPart (.function (.ident "unused") .nil none state .nil false none .nil .none)) .nil)

theorem explicit_mutability_unused (state : Option Mutability) :
    (declarationMutabilityUses (explicitMutabilityUnit state).env).map Prod.snd = state.toList ∧
    (syntaxMutabilityUses (explicitMutabilityUnit state)).map Prod.snd = state.toList := by
  cases state <;> exact ⟨rfl,rfl⟩

theorem mutability_carriers (state : Mutability) (payable : Bool) :
    [mutabilityFieldsAt (Syn.constructor .nil .nil payable none (.block .nil)),
     mutabilityFieldsAt (Syn.function (t := true) (.ident "f") .nil none (some state) .nil false none .nil .none),
     mutabilityFieldsAt (Syn.fallback .fbNoParams true (some state) .nil false none .none),
     mutabilityFieldsAt (Syn.receive true payable .nil false none .none),
     mutabilityFieldsAt (Syn.fnType .nil none (some state) .nil),
     mutabilityFieldsAt (Syn.stateVar (.elem .bool) (some .pub) (some .constant) none false "x" .none)] =
      [if payable then [.payable] else [],[state],[state],
       if payable then [.payable] else [],[state],[]] := by
  cases payable <;> rfl

/-- info: 'Solidity.Frontend.Admission.OccurrenceControls.explicit_mutability_unused' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms explicit_mutability_unused
/-- info: 'Solidity.Frontend.Admission.OccurrenceControls.mutability_carriers' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms mutability_carriers


/-! Regression: an import refusal must not truncate later visibility/mutability/payload diagnostics in an unused function. The old partial classifier deliberately remains silent on written visibility; this is a scope-gap control, not a legal or eligible execution witness. -/
def candidateUnusedFunction : Syn (.part true) :=
  .function (.ident "unused")
    (.cons (.param (.array (.elem .bool) (.some (.unaryPrefix .inc (.lit (.bool true)))))
      (some .memory) none) .nil)
    (some .pub) (some .view) .nil false none .nil .none

def candidateUnit : Syn .unit :=
  .unit (.cons (.importPath "p" none) (.cons (.topPart candidateUnusedFunction) .nil))

def candidateAccepts (f : Feature) : Bool :=
  decide (f ≠ .imports ∧ f ≠ .visibility ∧ f ≠ .stateMutability ∧ f ≠ .increments)

theorem candidate_refusals_not_truncated :
    (sourceCandidateRefusals candidateUnit candidateAccepts).map Prod.snd =
      [.imports,.visibility,.stateMutability,.increments] ∧
    sourceCandidateRefusal? candidateUnit candidateAccepts =
      some (⟨.top,Syn.importPath "p" none⟩,.imports) := ⟨rfl,rfl⟩

theorem old_subset_visibility_gap :
    sourceSubsetRefusal? candidateUnit (fun f => decide (f ≠ .visibility)) = none ∧
    sourceCandidateRefusal? candidateUnit (fun f => decide (f ≠ .visibility)) =
      some (⟨.part true,candidateUnusedFunction⟩,.visibility) := ⟨rfl,rfl⟩

/-- info: 'Solidity.Frontend.Admission.OccurrenceControls.candidate_refusals_not_truncated' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms candidate_refusals_not_truncated
/-- info: 'Solidity.Frontend.Admission.OccurrenceControls.old_subset_visibility_gap' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms old_subset_visibility_gap


/-! Regression: unused state declarations retain constant/immutable metadata; absent qualifiers stay absent. Contract/member declaration roots deliberately overlap, so declaration multiplicity differs from original-unit traversal. A top-level constant contributes its written keyword even though no optional qualifier field is present. Fixtures are syntax inventories, not legal initializer or write-once witnesses. -/
def explicitConstnessUnit (qualifier : Option Constness) : Syn .unit :=
  .unit (.cons (.contract false "C" .none .nil
    (.cons (.stateVar (.elem .bool) none qualifier none false "unused" .none) .nil)) .nil)

theorem explicit_constness_unused (qualifier : Option Constness) :
    (syntaxConstnessUses (explicitConstnessUnit qualifier)).map Prod.snd = qualifier.toList ∧
    (declarationConstnessUses (explicitConstnessUnit qualifier).env).map Prod.snd =
      qualifier.toList ++ qualifier.toList := by
  cases qualifier <;> exact ⟨rfl,rfl⟩

theorem constness_carriers (qualifier : Option Constness) :
    [constnessFieldsAt (Syn.stateVar (.elem .bool) none qualifier none false "x" .none),
     constnessFieldsAt (Syn.constant (.elem .bool) "x" (.lit (.bool true)))] =
      [qualifier.toList,[.constant]] := rfl

/-- info: 'Solidity.Frontend.Admission.OccurrenceControls.explicit_constness_unused' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms explicit_constness_unused
/-- info: 'Solidity.Frontend.Admission.OccurrenceControls.constness_carriers' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms constness_carriers


/-! Regression: an old candidate classifier can silently omit an unused constant qualifier; the explicit metadata feature classifier must retain its refusal. This syntax-only control claims no initializer legality or canonical admission. -/
theorem constness_diagnostic_gap :
    sourceCandidateRefusal? (explicitConstnessUnit (some .constant))
        (fun f => decide (f ≠ .constants)) = none ∧
    (syntaxFieldRefusals (explicitConstnessUnit (some .constant)) constnessFeaturesAt
        (fun f => decide (f ≠ .constants))).map Prod.snd = [.constants] := ⟨rfl,rfl⟩

/-- info: 'Solidity.Frontend.Admission.OccurrenceControls.constness_diagnostic_gap' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms constness_diagnostic_gap


def stateQualifierUnit (bases : Option (List IdPath)) (transient : Bool) : Syn .unit :=
  .unit (.cons (.contract false "C" .none .nil
    (.cons (.stateVar (.elem .bool) none none bases transient "unused" .none) .nil)) .nil)

theorem override_carriers :
    [declarationQualifierFeaturesAt (Syn.function (t := false) (.ident "f") .nil none none .nil
        false (some []) .nil .none),
     declarationQualifierFeaturesAt (.modifier "m" .none false (some []) .none),
     declarationQualifierFeaturesAt (.fallback .fbNoParams false none .nil false (some []) .none),
     declarationQualifierFeaturesAt (.receive false false .nil false (some []) .none),
     declarationQualifierFeaturesAt (.stateVar (.elem .bool) none none (some []) false "x" .none)] =
      List.replicate 5 [.overrideDeclarations] := rfl

theorem state_qualifier_combinations :
    [declarationQualifierFeaturesAt (.stateVar (.elem .bool) none none none false "x" .none),
     declarationQualifierFeaturesAt (.stateVar (.elem .bool) none none (some []) false "x" .none),
     declarationQualifierFeaturesAt (.stateVar (.elem .bool) none none none true "x" .none),
     declarationQualifierFeaturesAt (.stateVar (.elem .bool) none none (some []) true "x" .none)] =
      [[],[.overrideDeclarations],[.transientState],[.overrideDeclarations,.transientState]] := rfl

theorem qualifier_diagnostics :
    (syntaxFieldRefusals (stateQualifierUnit (some []) true) declarationQualifierFeaturesAt
      (fun _ => false)).map Prod.snd = [.overrideDeclarations,.transientState] ∧
    sourceCandidateRefusal? (stateQualifierUnit (some []) true)
      (fun f => decide (f ≠ .overrideDeclarations ∧ f ≠ .transientState)) = none := ⟨rfl,rfl⟩

/-- info: 'Solidity.Frontend.Admission.OccurrenceControls.override_carriers' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms override_carriers
/-- info: 'Solidity.Frontend.Admission.OccurrenceControls.state_qualifier_combinations' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms state_qualifier_combinations
/-- info: 'Solidity.Frontend.Admission.OccurrenceControls.qualifier_diagnostics' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms qualifier_diagnostics


/-! Regression: the new whole-unit diagnostic must retain all three metadata refusals even when the frozen old candidate is silent. This raw syntax fixture asserts no initializer/write-once, override or transient-storage legality and is not an admitted program. -/
def mixedMetadataState : Syn (.part false) :=
  .stateVar (.elem .bool) none (some .constant) (some []) true "unused" .none

def mixedMetadataUnit : Syn .unit :=
  .unit (.cons (.contract false "C" .none .nil (.cons mixedMetadataState .nil)) .nil)

def acceptsExceptMetadata (f : Solidity.Language.Feature) : Bool :=
  decide (f ≠ .constants ∧ f ≠ .overrideDeclarations ∧ f ≠ .transientState)

theorem metadata_v2_retains_all_refusals :
    (sourceCandidateMetadataV2Refusals mixedMetadataUnit acceptsExceptMetadata).map Prod.snd =
      [.constants,.overrideDeclarations,.transientState] ∧
    sourceCandidateMetadataV2Refusal? mixedMetadataUnit acceptsExceptMetadata =
      some (⟨.part false,mixedMetadataState⟩,.constants) ∧
    sourceCandidateRefusal? mixedMetadataUnit acceptsExceptMetadata = none := ⟨rfl,rfl,rfl⟩

/-- info: 'Solidity.Frontend.Admission.OccurrenceControls.metadata_v2_retains_all_refusals' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms metadata_v2_retains_all_refusals


/-! Regression: top-level and contract functions must not acquire the same dedicated marker. This syntax control retains generic/body markers and the frozen metadata-V2 omission; no legality, admission or eligible execution is claimed. -/
def functionCategoryNode (top : Bool) : Syn (.part top) :=
  .function (.ident "f") .nil none none .nil false none .nil (.some (.block .nil))

def freeFunctionUnit : Syn .unit := .unit (.cons (.topPart (functionCategoryNode true)) .nil)

theorem free_function_category_and_gap :
    freeFunctionFeaturesAt (functionCategoryNode true) = [.freeFunctions] ∧
    freeFunctionFeaturesAt (functionCategoryNode false) = [] ∧
    (syntaxFreeFunctionUses freeFunctionUnit).map Prod.snd = [.freeFunctions] ∧
    freeFunctionUnit.decls.map (fun d => (d.kind,d.top)) = [(.function,true)] ∧
    sourceCandidateMetadataV2Refusal? freeFunctionUnit
      (fun f => decide (f ≠ .freeFunctions)) = none := ⟨rfl,rfl,rfl,rfl,rfl⟩

/-- info: 'Solidity.Frontend.Admission.OccurrenceControls.free_function_category_and_gap' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms free_function_category_and_gap


/-! Regression: caller composition must report a free-function marker that the frozen candidate omits, retaining the actual typed source site and complete refusal list. This raw syntax control supplies no typing, admission or execution witness. -/
theorem free_function_composed_diagnostic :
    syntaxFieldRefusal? freeFunctionUnit
      (fun s => syntaxCandidateMetadataV2At s ++ freeFunctionFeaturesAt s)
      (fun f => decide (f ≠ .freeFunctions)) =
        some (⟨.part true,functionCategoryNode true⟩,.freeFunctions) ∧
    (syntaxFieldRefusals freeFunctionUnit
      (fun s => syntaxCandidateMetadataV2At s ++ freeFunctionFeaturesAt s)
      (fun f => decide (f ≠ .freeFunctions))).map Prod.snd = [.freeFunctions] ∧
    sourceCandidateMetadataV2Refusal? freeFunctionUnit
      (fun f => decide (f ≠ .freeFunctions)) = none := ⟨rfl,rfl,rfl⟩

/-- info: 'Solidity.Frontend.Admission.OccurrenceControls.free_function_composed_diagnostic' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms free_function_composed_diagnostic

end Solidity.Frontend.Admission.OccurrenceControls
