import Solidity.Frontend.Admission.ElementaryFeatures
import Solidity.Frontend.Admission.LocationFeatures

/-!
# A concrete structural feature subset from the original source unit

Regression: imports disappear from `unit.env`, while unused bodies and explicit
metadata must remain visible. This collector reuses `Syn.ctor`, the generated
generic projection, and the canonical intrinsic visitor; it adds no indexed
match or per-shape traversal. It combines selected payload-independent
constructor features with the existing elementary/location classifiers.
Calls, allocation, tuples, assembly, user/function types and pragmas need
payload/context-sensitive classification. Other missing metadata, lexical and
resolved features also remain open, even on marked constructors. Membership
bridges do not assert old/new order or multiplicity equality. Sites are
intrinsic subterm values, not unique positions or lexical scopes.
This subset never activates an admission
policy or certifies typing, execution or complete feature extraction.
-/
namespace Solidity.Frontend.Admission
open Solidity.Source Solidity.Language

/-- Selected payload-independent features. A missing marker is an extraction
gap, not evidence that the construct or a complete program is supported.
In particular, `.call` can be a conversion, and `.assembly` can be a canonical
rethrow; their payload-sensitive distinctions must not be guessed here. -/
def constructorFeature? : Ctor → Option Feature
  | .unit => some .sourceUnits
  | .importPath => some .imports
  | .importSymbols => some .imports
  | .importStar => some .imports
  | .contract => some .contracts
  | .interface => some .interfaces
  | .library => some .libraries
  | .inherit => some .inheritance
  | .constructor => some .constructors
  | .function => some .functions
  | .modifier => some .modifiers
  | .fallback => some .fallbackFunction
  | .receive => some .receiveFunction
  | .struct => some .structDeclarations
  | .enum => some .enumDeclarations
  | .udvt => some .valueTypeDeclarations
  | .stateVar => some .stateVariables
  | .constant => some .constants
  | .event => some .eventDeclarations
  | .error => some .errorDeclarations
  | .usingPart => some .usingFor
  | .named => some .namedArguments
  | .mapping => some .mappings
  | .varDecl => some .variableDeclarations
  | .index => some .indexAccess
  | .slice => some .rangeAccess
  | .member => some .memberAccess
  | .callOptions => some .callOptions
  | .payableConv => some .explicitConversions
  | .metaType => some .metaTypeExpression
  | .unarySuffix => some .increments
  | .exp => some .arithmetic
  | .mulDivMod => some .arithmetic
  | .addSub => some .arithmetic
  | .shift => some .shifts
  | .bitAnd => some .bitwise
  | .bitXor => some .bitwise
  | .bitOr => some .bitwise
  | .order => some .comparisons
  | .equality => some .comparisons
  | .and => some .shortCircuit
  | .or => some .shortCircuit
  | .cond => some .conditional
  | .assign => some .assignment
  | .inlineArray => some .inlineArrays
  | .litUnit => some .numericLiterals
  | .exprStmt => some .expressionStatements
  | .ifStmt => some .ifStatement
  | .forStmt => some .forStatement
  | .whileStmt => some .whileStatement
  | .doWhile => some .doWhileStatement
  | .continueStmt => some .continueStatement
  | .breakStmt => some .breakStatement
  | .tryStmt => some .tryStatement
  | .catchPlain => some .catchClauses
  | .catchSig => some .catchClauses
  | .returnStmt => some .returnStatement
  | .emit => some .emitStatement
  | .revert => some .revertStatement
  | .block => some .blocks
  | .uncheckedItem => some .uncheckedBlock
  | _ => none

/-- Combine actual constructor and metadata classifiers without changing
any of their existing definitions. No default locations are inferred. -/
def structuralFeaturesAt {c : Cat} (s : Syn c) : List Feature :=
  (constructorFeature? s.ctor).toList ++
    ((elementaryFieldsAt s).map elementaryFeature ++
      (dataLocationFieldsAt s).map dataLocationFeature)

/-- Every selected constructor marker is retained by the combined classifier. -/
theorem constructor_feature_covered {c : Cat} (s : Syn c) (f : Feature)
    (classified : constructorFeature? s.ctor = some f) :
    f ∈ structuralFeaturesAt s := by
  have present : f ∈ (constructorFeature? s.ctor).toList := by
    rw [classified]
    exact List.mem_singleton_self _
  exact List.mem_append.mpr (.inl present)

/-- Combining classifiers does not drop any explicit elementary field. -/
theorem elementary_feature_covered {c : Cat} (s : Syn c) (e : Elem)
    (present : e ∈ elementaryFieldsAt s) : elementaryFeature e ∈ structuralFeaturesAt s :=
  List.mem_append.mpr (.inr (List.mem_append.mpr (.inl
    (List.mem_map.mpr ⟨e,present,rfl⟩))))

/-- Combining classifiers does not drop any explicit data-location field. -/
theorem location_feature_covered {c : Cat} (s : Syn c) (loc : DataLoc)
    (present : DirectDataLocation s loc) : dataLocationFeature loc ∈ structuralFeaturesAt s :=
  List.mem_append.mpr (.inr (List.mem_append.mpr (.inr
    (List.mem_map.mpr ⟨loc,present.mem_fields,rfl⟩))))

/-- Whole-unit uses retain the original intrinsic site, including headers.
The caller cannot substitute a selected declaration or execution-root roster. -/
def sourceStructuralUses (unit : Syn .unit) : List (SyntaxOccurrence × Feature) :=
  (syntaxOccurrences unit).flatMap fun site =>
    (structuralFeaturesAt site.2).map fun feature => (site,feature)

/-- Exact uses against the independent original-unit subterm relation. -/
theorem sourceStructuralUses_iff (unit : Syn .unit) (site : SyntaxOccurrence) (f : Feature) :
    (site,f) ∈ sourceStructuralUses unit ↔
      Syn.Sub site ⟨.unit,unit⟩ ∧ f ∈ structuralFeaturesAt site.2 := by
  exact syntaxFieldUses_iff unit structuralFeaturesAt site f

/-- Ordered, duplicate-preserving projection of this explicitly partial
feature subset. This is not a Source admission certificate. -/
def sourceStructuralSubset (unit : Syn .unit) : List Feature :=
  (sourceStructuralUses unit).map Prod.snd

/-- A reported feature has an original intrinsic site and classifier witness;
every such subterm/classification contributes its feature. -/
theorem sourceStructuralSubset_iff (unit : Syn .unit) (f : Feature) :
    f ∈ sourceStructuralSubset unit ↔
      ∃ site : SyntaxOccurrence, Syn.Sub site ⟨.unit,unit⟩ ∧ f ∈ structuralFeaturesAt site.2 := by
  simp only [sourceStructuralSubset, List.mem_map]
  constructor
  · rintro ⟨⟨site,feature⟩,member,equality⟩
    have found := (sourceStructuralUses_iff unit site feature).mp member
    exact ⟨site,found.1,equality ▸ found.2⟩
  · rintro ⟨site,subterm,present⟩
    exact ⟨(site,f),(sourceStructuralUses_iff unit site f).mpr ⟨subterm,present⟩,rfl⟩

/-- The new whole-unit scan includes every elementary declaration feature
already certified by the declaration-aware collector. -/
theorem sourceStructuralSubset_elementary (unit : Syn .unit) (f : Feature)
    (present : f ∈ declarationElementaryFeatures unit.env) :
    f ∈ sourceStructuralSubset unit := by
  obtain ⟨site,e,member,field,classified⟩ :=
    declarationElementaryFeatures_source_witness unit f present
  apply (sourceStructuralSubset_iff unit f).mpr
  refine ⟨site,(syntaxOccurrences_iff unit site).mp member,?_⟩
  rw [← classified]
  exact elementary_feature_covered site.2 e field

/-- The new scan also includes every certified explicit-location feature. -/
theorem sourceStructuralSubset_location (unit : Syn .unit) (f : Feature)
    (present : f ∈ declarationLocationFeatures unit.env) :
    f ∈ sourceStructuralSubset unit := by
  obtain ⟨site,loc,member,field,classified⟩ :=
    declarationLocationFeatures_source_witness unit f present
  apply (sourceStructuralSubset_iff unit f).mpr
  refine ⟨site,(syntaxOccurrences_iff unit site).mp member,?_⟩
  rw [← classified]
  exact location_feature_covered site.2 loc field

/-- An import-only original unit guards header retention after environment
construction. This fixture asserts syntax features, not import resolution. -/
def structuralImportUnit (path : String) : Syn .unit :=
  .unit (.cons (.importPath path none) .nil)

/-- Header feature extraction is nonempty even without carried declarations. -/
theorem structuralImportUnit_features (path : String) :
    sourceStructuralSubset (structuralImportUnit path) = [.sourceUnits,.imports] := rfl

/-- The declaration environment erases this import, even though the original
unit's structural feature subset retains it. -/
theorem structuralImportUnit_env (path : String) :
    (structuralImportUnit path).env = (Syn.unit Syn.nil).env := rfl

/-- Exact limitation: this concrete subset cannot be reconstructed from the
declaration environment alone. The producer must retain the unit or
equivalent header information beyond `Env`; this API takes the original unit. -/
theorem sourceStructuralSubset_not_env_only :
    ¬ ∃ extract : Env → List Feature, ∀ unit : Syn .unit,
      extract unit.env = sourceStructuralSubset unit := by
  rintro ⟨extract,agrees⟩
  have empty := agrees (Syn.unit Syn.nil)
  have imported := agrees (structuralImportUnit "")
  rw [structuralImportUnit_env] at imported
  have impossible : ([.sourceUnits] : List Feature) = [.sourceUnits,.imports] :=
    empty.symm.trans imported
  exact (by decide : ([.sourceUnits] : List Feature) ≠ [.sourceUnits,.imports]) impossible

/-- Regression: no payload-sensitive interpretation is guessed from these
constructor tags, including conversion-versus-call and canonical rethrow. -/
theorem constructor_payload_gaps :
    ([.call,.new,.tuple,.assembly,.userType,.fnType,.pragma] : List Ctor).map constructorFeature? =
      [none,none,none,none,none,none,none] := rfl

/-- info: 'Solidity.Frontend.Admission.constructor_feature_covered' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms constructor_feature_covered
/-- info: 'Solidity.Frontend.Admission.elementary_feature_covered' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms elementary_feature_covered
/-- info: 'Solidity.Frontend.Admission.location_feature_covered' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms location_feature_covered
/-- info: 'Solidity.Frontend.Admission.sourceStructuralUses_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sourceStructuralUses_iff
/-- info: 'Solidity.Frontend.Admission.sourceStructuralSubset_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sourceStructuralSubset_iff
/-- info: 'Solidity.Frontend.Admission.sourceStructuralSubset_elementary' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sourceStructuralSubset_elementary
/-- info: 'Solidity.Frontend.Admission.sourceStructuralSubset_location' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sourceStructuralSubset_location
/-- info: 'Solidity.Frontend.Admission.structuralImportUnit_features' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms structuralImportUnit_features
/-- info: 'Solidity.Frontend.Admission.structuralImportUnit_env' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms structuralImportUnit_env
/-- info: 'Solidity.Frontend.Admission.sourceStructuralSubset_not_env_only' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms sourceStructuralSubset_not_env_only
/-- info: 'Solidity.Frontend.Admission.constructor_payload_gaps' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms constructor_payload_gaps

end Solidity.Frontend.Admission
