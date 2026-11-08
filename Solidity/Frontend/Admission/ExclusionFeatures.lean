import Solidity.Frontend.Admission.StructuralFeatures

/-! # Exclusion-aware syntax feature supplementation

Regression: unsigned right shift, removed units and general assembly must not lose their exclusion tags, while canonical rethrow must retain its existing exception. Reuse `Syn.excl` and the generic whole-syntax field collector. All six intrinsic exclusions have matching catalog IDs. Retain raw typed `Excl` diagnostics independently; feature extraction does not replace them. This does not replace `Syn.rejections`, choose a profile, establish typing or admission, or complete the remaining payload/lexical/resolved feature inventory. -/
namespace Solidity.Frontend.Admission
open Solidity.Source Solidity.Language


def exclusionFeature : Excl → Feature
  | .inlineAssembly => .inlineAssembly
  | .storageLayout => .storageLayout
  | .unsignedRightShift => .unsignedRightShift
  | .removedUnits => .removedUnits
  | .removedGenericSolidity => .removedGenericSolidity
  | .invalidModifierBody => .invalidModifierBody

/-- The mapping preserves the published identifier in every one of the six cases; it does not alter any catalog scope or admission status. -/
theorem exclusionFeature_id (exclusion : Excl) :
    (exclusionFeature exclusion).id = exclusion.id := by
  cases exclusion <;> rfl

/-- Metadata-only supplement. Canonical rethrow is distinguished using the existing root classifier; no new assembly shape parser is introduced. -/
def exclusionNodeFeatures (node : Node) : List Feature :=
  match node.excl with
  | some exclusion => [exclusionFeature exclusion]
  | none => if node.ctor = .assembly then [.canonicalRethrow] else []


def rootExclusionFeaturesAt {c : Cat} (s : Syn c) : List Feature :=
  exclusionNodeFeatures s.node


theorem root_exclusion_feature_covered {c : Cat} (s : Syn c) (exclusion : Excl)
    (excluded : s.excl = some exclusion) :
    exclusionFeature exclusion ∈ rootExclusionFeaturesAt s := by
  simp only [rootExclusionFeaturesAt, Syn.node, exclusionNodeFeatures, excluded,
    List.mem_singleton]

/-- Preserve the old canonical-rethrow exception for every assembly body. This is syntax classification, not the required bytes-memory typing evidence. -/
theorem assembly_exclusion_features {k : SCtx} (evmasm : Bool) (flags : List String)
    (body : Syn (.list .yulStmt)) :
    rootExclusionFeaturesAt (.assembly (k := k) evmasm flags body) =
      if isRethrow body then [.canonicalRethrow] else [.inlineAssembly] := by
  cases decision : isRethrow body <;>
    simp only [rootExclusionFeaturesAt, Syn.node, Syn.ctor, Syn.excl, decision,
      Bool.false_eq_true, if_false, if_true, exclusionNodeFeatures, exclusionFeature]

/-- All raw exclusion uses retain an actual typed site, independently of the catalog feature projection. No alternate declaration roster is supplied. -/
def syntaxExclusionUses {c : Cat} (root : Syn c) : List (SyntaxOccurrence × Excl) :=
  syntaxFieldUses root (fun node => node.excl.toList)


theorem syntaxExclusionUses_iff {c : Cat} (root : Syn c) (site : SyntaxOccurrence) (exclusion : Excl) :
    (site,exclusion) ∈ syntaxExclusionUses root ↔
      Syn.Sub site ⟨c,root⟩ ∧ site.2.excl = some exclusion := by
  simp only [syntaxExclusionUses, syntaxFieldUses_iff, Option.mem_toList]

/-- Every reported exclusion agrees with the existing intrinsic rejection channel. That channel remains independently available and unchanged. -/
theorem syntaxExclusionUses_reported {c : Cat} (root : Syn c) (site : SyntaxOccurrence)
    (exclusion : Excl) (reported : (site,exclusion) ∈ syntaxExclusionUses root) :
    exclusion ∈ root.rejections := by
  have found := (syntaxExclusionUses_iff root site exclusion).mp reported
  exact Syn.rejections_of_sub found.1 found.2

/-- Add the missing exclusion/rethrow tags to the earlier structural subset. Even this combined classifier remains partial and is not an admission policy. -/
def featuresWithExclusionsAt {c : Cat} (s : Syn c) : List Feature :=
  structuralFeaturesAt s ++ rootExclusionFeaturesAt s


def sourceFeaturesWithExclusions (unit : Syn .unit) : List Feature :=
  (syntaxFieldUses unit featuresWithExclusionsAt).map Prod.snd


theorem sourceFeaturesWithExclusions_iff (unit : Syn .unit) (f : Feature) :
    f ∈ sourceFeaturesWithExclusions unit ↔
      ∃ site : SyntaxOccurrence, Syn.Sub site ⟨.unit,unit⟩ ∧ f ∈ featuresWithExclusionsAt site.2 := by
  simp only [sourceFeaturesWithExclusions, List.mem_map]
  constructor
  · rintro ⟨⟨site,value⟩,member,equality⟩
    have found := (syntaxFieldUses_iff unit featuresWithExclusionsAt site value).mp member
    exact ⟨site,found.1,equality ▸ found.2⟩
  · rintro ⟨site,subterm,present⟩
    exact ⟨(site,f),(syntaxFieldUses_iff unit featuresWithExclusionsAt site f).mpr
      ⟨subterm,present⟩,rfl⟩

/-- The earlier certified structural/elementary/location features are retained by membership; no equality of ordering or multiplicity is asserted. -/
theorem sourceFeaturesWithExclusions_structural (unit : Syn .unit) (f : Feature)
    (present : f ∈ sourceStructuralSubset unit) : f ∈ sourceFeaturesWithExclusions unit := by
  obtain ⟨site,subterm,classified⟩ := (sourceStructuralSubset_iff unit f).mp present
  exact (sourceFeaturesWithExclusions_iff unit f).mpr
    ⟨site,subterm,List.mem_append.mpr (.inl classified)⟩


theorem sourceFeaturesWithExclusions_excluded (unit : Syn .unit) (site : SyntaxOccurrence)
    (exclusion : Excl) (subterm : Syn.Sub site ⟨.unit,unit⟩)
    (excluded : site.2.excl = some exclusion) :
    exclusionFeature exclusion ∈ sourceFeaturesWithExclusions unit :=
  (sourceFeaturesWithExclusions_iff unit (exclusionFeature exclusion)).mpr
    ⟨site,subterm,List.mem_append.mpr (.inr
      (root_exclusion_feature_covered site.2 exclusion excluded))⟩

/-- info: 'Solidity.Frontend.Admission.exclusionFeature_id' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms exclusionFeature_id
/-- info: 'Solidity.Frontend.Admission.root_exclusion_feature_covered' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms root_exclusion_feature_covered
/-- info: 'Solidity.Frontend.Admission.assembly_exclusion_features' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms assembly_exclusion_features
/-- info: 'Solidity.Frontend.Admission.syntaxExclusionUses_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms syntaxExclusionUses_iff
/-- info: 'Solidity.Frontend.Admission.syntaxExclusionUses_reported' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms syntaxExclusionUses_reported
/-- info: 'Solidity.Frontend.Admission.sourceFeaturesWithExclusions_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sourceFeaturesWithExclusions_iff
/-- info: 'Solidity.Frontend.Admission.sourceFeaturesWithExclusions_structural' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sourceFeaturesWithExclusions_structural
/-- info: 'Solidity.Frontend.Admission.sourceFeaturesWithExclusions_excluded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sourceFeaturesWithExclusions_excluded

end Solidity.Frontend.Admission
