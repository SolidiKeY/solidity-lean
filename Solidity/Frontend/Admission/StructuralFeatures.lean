import Solidity.Frontend.Admission.ElementaryFeatures
import Solidity.Frontend.Admission.LocationFeatures

/-! # A concrete structural feature subset from the original source unit

Regression: imports disappear from `unit.env`, while unused bodies and explicit metadata must remain visible. This collector reuses `Syn.ctor`, the generated generic projection, and the canonical intrinsic visitor; it adds no indexed match or per-shape traversal. It combines selected payload-independent constructor features with the existing elementary/location classifiers. Calls, allocation, tuples, assembly, user/function types and pragmas need payload/context-sensitive classification. Other missing metadata, lexical and resolved features also remain open, even on marked constructors. Membership bridges do not assert old/new order or multiplicity equality. Sites are intrinsic subterm values, not unique positions or lexical scopes. Override/transient metadata is inventoried from explicit keyword/flag presence, including an empty override list; it proves no override resolution, storage legality or inferred/default qualifier. This subset never activates an admission policy or certifies typing, execution or complete feature extraction. -/
namespace Solidity.Frontend.Admission
open Solidity.Source Solidity.Language

/-- Selected payload-independent features. A missing marker is an extraction gap, not evidence that the construct or a complete program is supported. In particular, `.call` can be a conversion, and `.assembly` can be a canonical rethrow; their payload-sensitive distinctions must not be guessed here. -/
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

/-- Combine actual constructor and metadata classifiers without changing any of their existing definitions. No default locations are inferred. -/
def structuralFeaturesAt {c : Cat} (s : Syn c) : List Feature :=
  (constructorFeature? s.ctor).toList ++
    ((elementaryFieldsAt s).map elementaryFeature ++
      (dataLocationFieldsAt s).map dataLocationFeature)


theorem constructor_feature_covered {c : Cat} (s : Syn c) (f : Feature)
    (classified : constructorFeature? s.ctor = some f) :
    f ∈ structuralFeaturesAt s := by
  have present : f ∈ (constructorFeature? s.ctor).toList := by
    rw [classified]
    exact List.mem_singleton_self _
  exact List.mem_append.mpr (.inl present)


theorem elementary_feature_covered {c : Cat} (s : Syn c) (e : Elem)
    (present : e ∈ elementaryFieldsAt s) : elementaryFeature e ∈ structuralFeaturesAt s :=
  List.mem_append.mpr (.inr (List.mem_append.mpr (.inl
    (List.mem_map.mpr ⟨e,present,rfl⟩))))


theorem location_feature_covered {c : Cat} (s : Syn c) (loc : DataLoc)
    (present : DirectDataLocation s loc) : dataLocationFeature loc ∈ structuralFeaturesAt s :=
  List.mem_append.mpr (.inr (List.mem_append.mpr (.inr
    (List.mem_map.mpr ⟨loc,present.mem_fields,rfl⟩))))

/-- Whole-unit uses retain the original intrinsic site, including headers. The caller cannot substitute a selected declaration or execution-root roster. -/
def sourceStructuralUses (unit : Syn .unit) : List (SyntaxOccurrence × Feature) :=
  (syntaxOccurrences unit).flatMap fun site =>
    (structuralFeaturesAt site.2).map fun feature => (site,feature)


theorem sourceStructuralUses_iff (unit : Syn .unit) (site : SyntaxOccurrence) (f : Feature) :
    (site,f) ∈ sourceStructuralUses unit ↔
      Syn.Sub site ⟨.unit,unit⟩ ∧ f ∈ structuralFeaturesAt site.2 := by
  exact syntaxFieldUses_iff unit structuralFeaturesAt site f

/-- Ordered, duplicate-preserving projection of this explicitly partial feature subset. This is not a Source admission certificate. -/
def sourceStructuralSubset (unit : Syn .unit) : List Feature :=
  (sourceStructuralUses unit).map Prod.snd

/-- A reported feature has an original intrinsic site and classifier witness; every such subterm/classification contributes its feature. -/
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


theorem sourceStructuralSubset_elementary (unit : Syn .unit) (f : Feature)
    (present : f ∈ declarationElementaryFeatures unit.env) :
    f ∈ sourceStructuralSubset unit := by
  obtain ⟨site,e,member,field,classified⟩ :=
    declarationElementaryFeatures_source_witness unit f present
  apply (sourceStructuralSubset_iff unit f).mpr
  refine ⟨site,(syntaxOccurrences_iff unit site).mp member,?_⟩
  rw [← classified]
  exact elementary_feature_covered site.2 e field


theorem sourceStructuralSubset_location (unit : Syn .unit) (f : Feature)
    (present : f ∈ declarationLocationFeatures unit.env) :
    f ∈ sourceStructuralSubset unit := by
  obtain ⟨site,loc,member,field,classified⟩ :=
    declarationLocationFeatures_source_witness unit f present
  apply (sourceStructuralSubset_iff unit f).mpr
  refine ⟨site,(syntaxOccurrences_iff unit site).mp member,?_⟩
  rw [← classified]
  exact location_feature_covered site.2 loc field

/-- An import-only original unit guards header retention after environment construction. This fixture asserts syntax features, not import resolution. -/
def structuralImportUnit (path : String) : Syn .unit :=
  .unit (.cons (.importPath path none) .nil)


theorem structuralImportUnit_features (path : String) :
    sourceStructuralSubset (structuralImportUnit path) = [.sourceUnits,.imports] := rfl


theorem structuralImportUnit_env (path : String) :
    (structuralImportUnit path).env = (Syn.unit Syn.nil).env := rfl

/-- Exact limitation: this concrete subset cannot be reconstructed from the declaration environment alone. The producer must retain the unit or equivalent header information beyond `Env`; this API takes the original unit. -/
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

/-- Regression: no payload-sensitive interpretation is guessed from these constructor tags, including conversion-versus-call and canonical rethrow. -/
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

/-! Literal payload tags must survive collection even in unused syntax. These markers classify the existing intrinsic literal form only: lexical spelling, UTF-8 validity, contextual address classification, exact constant folding and admission are not inferred from decoded bytes or a numeric value. -/


def literalFeature : Lit → Feature
  | .str _ => .stringLiterals
  | .hexStr _ => .hexLiterals
  | .unicodeStr _ => .unicodeLiterals
  | .bool _ => .booleanLiterals
  | .num _ => .numericLiterals

/-- Direct literal fields; descendants are handled by the canonical visitor. A denomination also contains a numeric literal, but its unit feature is separate. -/
def literalFeaturesAt {c : Cat} (s : Syn c) : List Feature :=
  Syn.casesOn (motive := fun _ _ => List Feature) s
    ([])
    (fun _ _ => [])
    ([])
    (fun _ => [])
    (fun _ => [])
    (fun _ => [])
    (fun _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ => [])
    (fun _ _ => [])
    (fun _ _ _ _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ => [])
    (fun _ => [])
    (fun _ _ => [])
    (fun _ _ _ _ _ => [])
    (fun _ _ _ _ _ _ _ _ _ => [])
    (fun _ _ _ _ _ => [])
    (fun _ _ _ _ _ _ _ => [])
    ([])
    (fun _ _ _ => [])
    (fun _ _ _ _ _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ => [])
    (fun _ _ _ _ _ _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ => [])
    (fun _ _ => [])
    (fun _ => [])
    (fun _ _ _ => [])
    (fun _ _ _ _ => [])
    (fun _ _ => [])
    (fun _ => [])
    (fun _ => [])
    (fun _ _ => [])
    (fun _ _ => [])
    (fun _ _ _ => [])
    (fun _ => [])
    (fun _ _ _ _ => [])
    (fun _ _ _ _ => [])
    (fun _ => [])
    (fun _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ => [])
    (fun _ => [])
    (fun _ => [])
    (fun _ _ => [])
    (fun _ _ => [])
    (fun _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ => [])
    (fun _ _ => [])
    (fun _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ => [])
    (fun _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ _ => [])
    (fun _ => [])
    (fun _ _ => [])
    (fun _ _ => [])
    (fun _ => [])
    (fun value => [literalFeature value])
    (fun _ _ => [.numericLiterals])
    (fun _ _ => [])
    (fun _ _ => [])
    (fun _ _ _ _ => [])
    (fun _ => [])
    (fun _ => [])
    (fun _ => [])
    (fun _ _ _ => [])
    (fun _ _ _ _ => [])
    (fun _ _ => [])
    (fun _ _ => [])
    ([])
    ([])
    (fun _ _ _ _ _ => [])
    (fun _ => [])
    (fun _ _ _ _ => [])
    (fun _ => [])
    (fun _ _ => [])
    (fun _ _ => [])
    (fun _ _ _ => [])
    (fun _ => [])
    (fun _ => [])
    (fun _ => [])
    (fun _ => [])
    (fun _ _ _ => [])
    (fun _ _ _ => [])
    (fun _ => [])
    (fun _ _ => [])
    (fun _ _ _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ => [])
    ([])
    ([])
    ([])
    (fun _ _ _ _ => [])
    (fun _ _ => [])
    (fun _ _ => [])
    (fun _ => [])


def syntaxLiteralUses {c : Cat} (root : Syn c) : List (SyntaxOccurrence × Feature) :=
  syntaxFieldUses root literalFeaturesAt

theorem syntaxLiteralUses_iff {c : Cat} (root : Syn c) (site : SyntaxOccurrence)
    (f : Feature) :
    (site,f) ∈ syntaxLiteralUses root ↔
      Syn.Sub site ⟨c,root⟩ ∧ f ∈ literalFeaturesAt site.2 :=
  syntaxFieldUses_iff root literalFeaturesAt site f

/-- Equal decoded byte payloads retain their distinct intrinsic literal tags. This is not a proof that any byte sequence is well formed or admitted. -/
theorem literal_payload_tags (bytes : List UInt8) (b : Bool) (n : NumLit) :
    ([Lit.str bytes,.hexStr bytes,.unicodeStr bytes,.bool b,.num n].map literalFeature) =
      [.stringLiterals,.hexLiterals,.unicodeLiterals,.booleanLiterals,.numericLiterals] := rfl


theorem literal_root_uses (l : Lit) (n : NumLit) (u : Denom) :
    syntaxLiteralUses (.lit l) = [(⟨_,.lit l⟩,literalFeature l)] ∧
    syntaxLiteralUses (.litUnit n u) = [(⟨_,.litUnit n u⟩,.numericLiterals)] := ⟨rfl,rfl⟩

/-- info: 'Solidity.Frontend.Admission.syntaxLiteralUses_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms syntaxLiteralUses_iff
/-- info: 'Solidity.Frontend.Admission.literal_payload_tags' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms literal_payload_tags
/-- info: 'Solidity.Frontend.Admission.literal_root_uses' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms literal_root_uses


/-! Regression: identical constructor tags must retain prefix/compound/unit distinctions, including removed years. These are intrinsic syntax markers, not typing, arithmetic/folding, lvalue scheduling, lexical validity or admission proofs. Compose through the generic collector; old subsets stay frozen. -/
def prefixFeature : PrefixOp → Feature
  | .inc | .dec => .increments
  | .not | .bitNot | .neg => .unaryArithmetic
  | .delete => .deleteExpression

def assignmentPayloadFeatures : AssignOp → List Feature
  | .assign => []
  | .bitOr | .bitXor | .bitAnd | .shl | .sar | .shr | .add | .sub | .mul | .div | .mod =>
      [.compoundAssignment]

def denominationFeature : Denom → Feature
  | .wei | .gwei | .ether => .etherUnits
  | .seconds | .minutes | .hours | .days | .weeks => .timeUnits
  | .years => .removedUnits

def payloadFeaturesAt {c : Cat} (s : Syn c) : List Feature :=
  Syn.casesOn (motive := fun _ _ => List Feature) s
    ([])
    (fun _ _ => [])
    ([])
    (fun _ => [])
    (fun _ => [])
    (fun _ => [])
    (fun _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ => [])
    (fun _ _ => [])
    (fun _ _ _ _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ => [])
    (fun _ => [])
    (fun _ _ => [])
    (fun _ _ _ _ _ => [])
    (fun _ _ _ _ _ _ _ _ _ => [])
    (fun _ _ _ _ _ => [])
    (fun _ _ _ _ _ _ _ => [])
    ([])
    (fun _ _ _ => [])
    (fun _ _ _ _ _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ => [])
    (fun _ _ _ _ _ _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ => [])
    (fun _ _ => [])
    (fun _ => [])
    (fun _ _ _ => [])
    (fun _ _ _ _ => [])
    (fun _ _ => [])
    (fun _ => [])
    (fun _ => [])
    (fun _ _ => [])
    (fun _ _ => [])
    (fun _ _ _ => [])
    (fun _ => [])
    (fun _ _ _ _ => [])
    (fun _ _ _ _ => [])
    (fun _ => [])
    (fun _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ => [])
    (fun _ => [])
    (fun _ => [])
    (fun op _ => [prefixFeature op])
    (fun _ _ => [])
    (fun _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ => [])
    (fun _ _ => [])
    (fun _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ => [])
    (fun _ _ => [])
    (fun _ _ _ => [])
    (fun op _ _ => assignmentPayloadFeatures op)
    (fun _ => [])
    (fun _ _ => [])
    (fun _ _ => [])
    (fun _ => [])
    (fun _ => [])
    (fun _ unit => [denominationFeature unit])
    (fun _ _ => [])
    (fun _ _ => [])
    (fun _ _ _ _ => [])
    (fun _ => [])
    (fun _ => [])
    (fun _ => [])
    (fun _ _ _ => [])
    (fun _ _ _ _ => [])
    (fun _ _ => [])
    (fun _ _ => [])
    ([])
    ([])
    (fun _ _ _ _ _ => [])
    (fun _ => [])
    (fun _ _ _ _ => [])
    (fun _ => [])
    (fun _ _ => [])
    (fun _ _ => [])
    (fun _ _ _ => [])
    (fun _ => [])
    (fun _ => [])
    (fun _ => [])
    (fun _ => [])
    (fun _ _ _ => [])
    (fun _ _ _ => [])
    (fun _ => [])
    (fun _ _ => [])
    (fun _ _ _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ => [])
    ([])
    ([])
    ([])
    (fun _ _ _ _ => [])
    (fun _ _ => [])
    (fun _ _ => [])
    (fun _ => [])

def syntaxPayloadUses {c : Cat} (root : Syn c) : List (SyntaxOccurrence × Feature) :=
  syntaxFieldUses root payloadFeaturesAt

theorem syntaxPayloadUses_iff {c : Cat} (root : Syn c) (site : SyntaxOccurrence) (f : Feature) :
    (site,f) ∈ syntaxPayloadUses root ↔ Syn.Sub site ⟨c,root⟩ ∧ f ∈ payloadFeaturesAt site.2 :=
  syntaxFieldUses_iff root payloadFeaturesAt site f

theorem prefix_payload_tags :
    ([PrefixOp.inc,.dec,.not,.bitNot,.delete,.neg].map prefixFeature) =
      [.increments,.increments,.unaryArithmetic,.unaryArithmetic,.deleteExpression,.unaryArithmetic] := rfl

theorem denomination_payload_tags :
    ([Denom.wei,.gwei,.ether,.seconds,.minutes,.hours,.days,.weeks,.years].map denominationFeature) =
      [.etherUnits,.etherUnits,.etherUnits,.timeUnits,.timeUnits,.timeUnits,.timeUnits,.timeUnits,.removedUnits] := rfl

theorem assignment_payload_none_iff (op : AssignOp) :
    assignmentPayloadFeatures op = [] ↔ op = .assign := by
  cases op <;> decide

/-- info: 'Solidity.Frontend.Admission.syntaxPayloadUses_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms syntaxPayloadUses_iff
/-- info: 'Solidity.Frontend.Admission.prefix_payload_tags' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms prefix_payload_tags
/-- info: 'Solidity.Frontend.Admission.denomination_payload_tags' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms denomination_payload_tags
/-- info: 'Solidity.Frontend.Admission.assignment_payload_none_iff' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms assignment_payload_none_iff


/-! Regression: visibility is metadata, so constructor-only traversal misses explicit fields in unused declarations and function types. Account for all six carriers through the generic visitor. Omission stays absent; legacy constructor visibility and syntactically invalid function-type visibility remain raw syntax evidence, not defaults, legality, admission or dispatch proofs. -/
def ctorVisibility : CtorVis → Visibility
  | .internal => .internal
  | .pub => .pub

def stateVisibility : StateVis → Visibility
  | .pub => .pub
  | .priv => .priv
  | .internal => .internal

inductive DirectVisibility : {c : Cat} → Syn c → Visibility → Prop where
  | constructor (params mods payable body) (v : CtorVis) :
      DirectVisibility (.constructor params mods payable (some v) body) (ctorVisibility v)
  | function {t : Bool} (name params mutability mods virtual override returns body) (v : Visibility) :
      DirectVisibility (.function (t := t) name params (some v) mutability mods virtual override returns body) v
  | fallback (sig mutability mods virtual override body) :
      DirectVisibility (.fallback sig true mutability mods virtual override body) .external
  | receive (payable mods virtual override body) :
      DirectVisibility (.receive true payable mods virtual override body) .external
  | stateVar (ty const override transient name init) (v : StateVis) :
      DirectVisibility (.stateVar ty (some v) const override transient name init) (stateVisibility v)
  | fnType (params mutability returns) (v : Visibility) :
      DirectVisibility (.fnType params (some v) mutability returns) v

def visibilityFieldsAt {c : Cat} (s : Syn c) : List Visibility :=
  Syn.casesOn (motive := fun _ _ => List Visibility) s
    ([])
    (fun _ _ => [])
    ([])
    (fun _ => [])
    (fun _ => [])
    (fun _ => [])
    (fun _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ => [])
    (fun _ _ => [])
    (fun _ _ _ _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ => [])
    (fun _ => [])
    (fun _ _ => [])
    (fun _ _ _ vis _ => vis.toList.map ctorVisibility)
    (fun _ _ vis _ _ _ _ _ _ => vis.toList)
    (fun _ _ _ _ _ => [])
    (fun _ external _ _ _ _ _ => if external then [.external] else [])
    ([])
    (fun _ _ _ => [])
    (fun external _ _ _ _ _ => if external then [.external] else [])
    (fun _ _ _ => [])
    (fun _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ => [])
    (fun _ vis _ _ _ _ _ => vis.toList.map stateVisibility)
    (fun _ _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ => [])
    (fun _ _ => [])
    (fun _ => [])
    (fun _ _ _ => [])
    (fun _ _ _ _ => [])
    (fun _ _ => [])
    (fun _ => [])
    (fun _ => [])
    (fun _ _ => [])
    (fun _ _ => [])
    (fun _ _ _ => [])
    (fun _ => [])
    (fun _ vis _ _ => vis.toList)
    (fun _ _ _ _ => [])
    (fun _ => [])
    (fun _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ => [])
    (fun _ => [])
    (fun _ => [])
    (fun _ _ => [])
    (fun _ _ => [])
    (fun _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ => [])
    (fun _ _ => [])
    (fun _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ => [])
    (fun _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ _ => [])
    (fun _ => [])
    (fun _ _ => [])
    (fun _ _ => [])
    (fun _ => [])
    (fun _ => [])
    (fun _ _ => [])
    (fun _ _ => [])
    (fun _ _ => [])
    (fun _ _ _ _ => [])
    (fun _ => [])
    (fun _ => [])
    (fun _ => [])
    (fun _ _ _ => [])
    (fun _ _ _ _ => [])
    (fun _ _ => [])
    (fun _ _ => [])
    ([])
    ([])
    (fun _ _ _ _ _ => [])
    (fun _ => [])
    (fun _ _ _ _ => [])
    (fun _ => [])
    (fun _ _ => [])
    (fun _ _ => [])
    (fun _ _ _ => [])
    (fun _ => [])
    (fun _ => [])
    (fun _ => [])
    (fun _ => [])
    (fun _ _ _ => [])
    (fun _ _ _ => [])
    (fun _ => [])
    (fun _ _ => [])
    (fun _ _ _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ => [])
    ([])
    ([])
    ([])
    (fun _ _ _ _ => [])
    (fun _ _ => [])
    (fun _ _ => [])
    (fun _ => [])

theorem DirectVisibility.mem_fields {c : Cat} {s : Syn c} {v : Visibility}
    (field : DirectVisibility s v) : v ∈ visibilityFieldsAt s := by
  cases field <;> exact List.mem_singleton_self _

theorem visibilityFieldsAt_sound {c : Cat} (s : Syn c) (v : Visibility)
    (present : v ∈ visibilityFieldsAt s) : DirectVisibility s v := by
  cases s with
  | constructor params mods payable vis body =>
    cases vis with
    | none => exact False.elim (List.not_mem_nil present)
    | some value =>
      have same := List.mem_singleton.mp present
      cases same
      exact .constructor params mods payable body value
  | function name params vis mutability mods virtual override returns body =>
    cases vis with
    | none => exact False.elim (List.not_mem_nil present)
    | some value =>
      have same := List.mem_singleton.mp present
      cases same
      exact .function name params mutability mods virtual override returns body _
  | fallback sig external mutability mods virtual override body =>
    cases external with
    | false => exact False.elim (List.not_mem_nil present)
    | true =>
      have same := List.mem_singleton.mp present
      cases same
      exact .fallback sig mutability mods virtual override body
  | receive external payable mods virtual override body =>
    cases external with
    | false => exact False.elim (List.not_mem_nil present)
    | true =>
      have same := List.mem_singleton.mp present
      cases same
      exact .receive payable mods virtual override body
  | stateVar ty vis const override transient name init =>
    cases vis with
    | none => exact False.elim (List.not_mem_nil present)
    | some value =>
      have same := List.mem_singleton.mp present
      cases same
      exact .stateVar ty const override transient name init value
  | fnType params vis mutability returns =>
    cases vis with
    | none => exact False.elim (List.not_mem_nil present)
    | some value =>
      have same := List.mem_singleton.mp present
      cases same
      exact .fnType params mutability returns _
  | _ => exact False.elim (List.not_mem_nil present)

theorem visibilityFieldsAt_iff {c : Cat} (s : Syn c) (v : Visibility) :
    v ∈ visibilityFieldsAt s ↔ DirectVisibility s v :=
  ⟨visibilityFieldsAt_sound s v,DirectVisibility.mem_fields⟩

def syntaxVisibilityUses {c : Cat} (root : Syn c) : List (SyntaxOccurrence × Visibility) :=
  syntaxFieldUses root visibilityFieldsAt

theorem syntaxVisibilityUses_iff {c : Cat} (root : Syn c) (site : SyntaxOccurrence) (v : Visibility) :
    (site,v) ∈ syntaxVisibilityUses root ↔ Syn.Sub site ⟨c,root⟩ ∧ DirectVisibility site.2 v := by
  rw [syntaxVisibilityUses, syntaxFieldUses_iff, visibilityFieldsAt_iff]

def declarationVisibilityUses (E : Env) : List (DeclarationOccurrence × Visibility) :=
  declarationFieldUses E visibilityFieldsAt

theorem declarationVisibilityUses_iff (E : Env) (site : DeclarationOccurrence) (v : Visibility) :
    (site,v) ∈ declarationVisibilityUses E ↔ site.Occurs E ∧ DirectVisibility site.2.2 v := by
  rw [declarationVisibilityUses, declarationFieldUses_iff, visibilityFieldsAt_iff]

/-- info: 'Solidity.Frontend.Admission.visibilityFieldsAt_iff' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms visibilityFieldsAt_iff
/-- info: 'Solidity.Frontend.Admission.syntaxVisibilityUses_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms syntaxVisibilityUses_iff
/-- info: 'Solidity.Frontend.Admission.declarationVisibilityUses_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms declarationVisibilityUses_iff


def visibilityFeaturesAt {c : Cat} (s : Syn c) : List Feature :=
  (visibilityFieldsAt s).map fun _ => .visibility

theorem visibilityFeaturesAt_iff {c : Cat} (s : Syn c) (f : Feature) :
    f ∈ visibilityFeaturesAt s ↔ f = .visibility ∧ ∃ v, DirectVisibility s v := by
  change (f ∈ (visibilityFieldsAt s).map (fun _ => Feature.visibility)) ↔ _
  rw [List.mem_map]
  constructor
  · rintro ⟨v,field,equal⟩
    exact ⟨equal.symm, v, (visibilityFieldsAt_iff s v).mp field⟩
  · rintro ⟨rfl,v,field⟩
    exact ⟨v,(visibilityFieldsAt_iff s v).mpr field,rfl⟩

/-- info: 'Solidity.Frontend.Admission.visibilityFeaturesAt_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms visibilityFeaturesAt_iff


/-! Regression: written mutability on unused declarations and function types is metadata, not a child. The five carriers use the shared syntax visitor. Absent/false stays empty; state-variable getters must not invent written pure/view qualifiers. This raw inventory proves neither mutability legality, effects, nonpayable entry checks nor admission. -/
inductive DirectMutability : {c : Cat} → Syn c → Mutability → Prop where
  | constructor (params mods vis body) :
      DirectMutability (.constructor params mods true vis body) .payable
  | function {t : Bool} (name params vis mods virtual override returns body) (state : Mutability) :
      DirectMutability (.function (t := t) name params vis (some state) mods virtual override returns body) state
  | fallback (sig external mods virtual override body) (state : Mutability) :
      DirectMutability (.fallback sig external (some state) mods virtual override body) state
  | receive (external mods virtual override body) :
      DirectMutability (.receive external true mods virtual override body) .payable
  | fnType (params vis returns) (state : Mutability) :
      DirectMutability (.fnType params vis (some state) returns) state

def mutabilityFieldsAt {c : Cat} (s : Syn c) : List Mutability :=
  Syn.casesOn (motive := fun _ _ => List Mutability) s
    ([])
    (fun _ _ => [])
    ([])
    (fun _ => [])
    (fun _ => [])
    (fun _ => [])
    (fun _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ => [])
    (fun _ _ => [])
    (fun _ _ _ _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ => [])
    (fun _ => [])
    (fun _ _ => [])
    (fun _ _ payable _ _ => if payable then [.payable] else [])
    (fun _ _ _ state _ _ _ _ _ => state.toList)
    (fun _ _ _ _ _ => [])
    (fun _ _ state _ _ _ _ => state.toList)
    ([])
    (fun _ _ _ => [])
    (fun _ payable _ _ _ _ => if payable then [.payable] else [])
    (fun _ _ _ => [])
    (fun _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ => [])
    (fun _ _ _ _ _ _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ => [])
    (fun _ _ => [])
    (fun _ => [])
    (fun _ _ _ => [])
    (fun _ _ _ _ => [])
    (fun _ _ => [])
    (fun _ => [])
    (fun _ => [])
    (fun _ _ => [])
    (fun _ _ => [])
    (fun _ _ _ => [])
    (fun _ => [])
    (fun _ _ state _ => state.toList)
    (fun _ _ _ _ => [])
    (fun _ => [])
    (fun _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ => [])
    (fun _ => [])
    (fun _ => [])
    (fun _ _ => [])
    (fun _ _ => [])
    (fun _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ => [])
    (fun _ _ => [])
    (fun _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ => [])
    (fun _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ _ => [])
    (fun _ => [])
    (fun _ _ => [])
    (fun _ _ => [])
    (fun _ => [])
    (fun _ => [])
    (fun _ _ => [])
    (fun _ _ => [])
    (fun _ _ => [])
    (fun _ _ _ _ => [])
    (fun _ => [])
    (fun _ => [])
    (fun _ => [])
    (fun _ _ _ => [])
    (fun _ _ _ _ => [])
    (fun _ _ => [])
    (fun _ _ => [])
    ([])
    ([])
    (fun _ _ _ _ _ => [])
    (fun _ => [])
    (fun _ _ _ _ => [])
    (fun _ => [])
    (fun _ _ => [])
    (fun _ _ => [])
    (fun _ _ _ => [])
    (fun _ => [])
    (fun _ => [])
    (fun _ => [])
    (fun _ => [])
    (fun _ _ _ => [])
    (fun _ _ _ => [])
    (fun _ => [])
    (fun _ _ => [])
    (fun _ _ _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ => [])
    ([])
    ([])
    ([])
    (fun _ _ _ _ => [])
    (fun _ _ => [])
    (fun _ _ => [])
    (fun _ => [])

theorem DirectMutability.mem_fields {c : Cat} {s : Syn c} {state : Mutability}
    (field : DirectMutability s state) : state ∈ mutabilityFieldsAt s := by
  cases field <;> exact List.mem_singleton_self _

theorem mutabilityFieldsAt_sound {c : Cat} (s : Syn c) (state : Mutability)
    (present : state ∈ mutabilityFieldsAt s) : DirectMutability s state := by
  cases s with
  | constructor params mods payable vis body =>
    cases payable with
    | false => exact False.elim (List.not_mem_nil present)
    | true =>
      have same := List.mem_singleton.mp present
      cases same
      exact .constructor params mods vis body
  | function name params vis stateOpt mods virtual override returns body =>
    cases stateOpt with
    | none => exact False.elim (List.not_mem_nil present)
    | some value =>
      have same := List.mem_singleton.mp present
      cases same
      exact .function name params vis mods virtual override returns body _
  | fallback sig external stateOpt mods virtual override body =>
    cases stateOpt with
    | none => exact False.elim (List.not_mem_nil present)
    | some value =>
      have same := List.mem_singleton.mp present
      cases same
      exact .fallback sig external mods virtual override body _
  | receive external payable mods virtual override body =>
    cases payable with
    | false => exact False.elim (List.not_mem_nil present)
    | true =>
      have same := List.mem_singleton.mp present
      cases same
      exact .receive external mods virtual override body
  | fnType params vis stateOpt returns =>
    cases stateOpt with
    | none => exact False.elim (List.not_mem_nil present)
    | some value =>
      have same := List.mem_singleton.mp present
      cases same
      exact .fnType params vis returns _
  | _ => exact False.elim (List.not_mem_nil present)

theorem mutabilityFieldsAt_iff {c : Cat} (s : Syn c) (state : Mutability) :
    state ∈ mutabilityFieldsAt s ↔ DirectMutability s state :=
  ⟨mutabilityFieldsAt_sound s state,DirectMutability.mem_fields⟩

def syntaxMutabilityUses {c : Cat} (root : Syn c) : List (SyntaxOccurrence × Mutability) :=
  syntaxFieldUses root mutabilityFieldsAt

theorem syntaxMutabilityUses_iff {c : Cat} (root : Syn c) (site : SyntaxOccurrence) (state : Mutability) :
    (site,state) ∈ syntaxMutabilityUses root ↔ Syn.Sub site ⟨c,root⟩ ∧ DirectMutability site.2 state := by
  rw [syntaxMutabilityUses, syntaxFieldUses_iff, mutabilityFieldsAt_iff]

def declarationMutabilityUses (E : Env) : List (DeclarationOccurrence × Mutability) :=
  declarationFieldUses E mutabilityFieldsAt

theorem declarationMutabilityUses_iff (E : Env) (site : DeclarationOccurrence) (state : Mutability) :
    (site,state) ∈ declarationMutabilityUses E ↔ site.Occurs E ∧ DirectMutability site.2.2 state := by
  rw [declarationMutabilityUses, declarationFieldUses_iff, mutabilityFieldsAt_iff]

def mutabilityFeaturesAt {c : Cat} (s : Syn c) : List Feature :=
  (mutabilityFieldsAt s).map fun _ => .stateMutability

theorem mutabilityFeaturesAt_iff {c : Cat} (s : Syn c) (f : Feature) :
    f ∈ mutabilityFeaturesAt s ↔ f = .stateMutability ∧ ∃ state, DirectMutability s state := by
  change (f ∈ (mutabilityFieldsAt s).map (fun _ => Feature.stateMutability)) ↔ _
  rw [List.mem_map]
  constructor
  · rintro ⟨state,field,equal⟩
    exact ⟨equal.symm, state, (mutabilityFieldsAt_iff s state).mp field⟩
  · rintro ⟨rfl,state,field⟩
    exact ⟨state,(mutabilityFieldsAt_iff s state).mpr field,rfl⟩

/-- info: 'Solidity.Frontend.Admission.mutabilityFieldsAt_iff' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms mutabilityFieldsAt_iff
/-- info: 'Solidity.Frontend.Admission.syntaxMutabilityUses_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms syntaxMutabilityUses_iff
/-- info: 'Solidity.Frontend.Admission.declarationMutabilityUses_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms declarationMutabilityUses_iff
/-- info: 'Solidity.Frontend.Admission.mutabilityFeaturesAt_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mutabilityFeaturesAt_iff


/-! Regression: constructor-only tags miss written constant/immutable state-variable qualifiers; top-level constant syntax must also remain visible. The two actual carriers reuse the generic visitor. Omission is not inferred mutable/constant status, and these raw markers certify no initializer, write-once, location, typing or admission rule. -/
inductive DirectConstness : {c : Cat} → Syn c → Constness → Prop where
  | stateVar (ty vis override transient name init) (qualifier : Constness) :
      DirectConstness (.stateVar ty vis (some qualifier) override transient name init) qualifier
  | constant (ty name value) : DirectConstness (.constant ty name value) .constant

def constnessFieldsAt {c : Cat} (s : Syn c) : List Constness :=
  Syn.casesOn (motive := fun _ _ => List Constness) s
    ([])
    (fun _ _ => [])
    ([])
    (fun _ => [])
    (fun _ => [])
    (fun _ => [])
    (fun _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ => [])
    (fun _ _ => [])
    (fun _ _ _ _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ => [])
    (fun _ => [])
    (fun _ _ => [])
    (fun _ _ _ _ _ => [])
    (fun _ _ _ _ _ _ _ _ _ => [])
    (fun _ _ _ _ _ => [])
    (fun _ _ _ _ _ _ _ => [])
    ([])
    (fun _ _ _ => [])
    (fun _ _ _ _ _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ => [])
    (fun _ _ qualifier _ _ _ _ => qualifier.toList)
    (fun _ _ _ => [.constant])
    (fun _ _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ => [])
    (fun _ _ => [])
    (fun _ => [])
    (fun _ _ _ => [])
    (fun _ _ _ _ => [])
    (fun _ _ => [])
    (fun _ => [])
    (fun _ => [])
    (fun _ _ => [])
    (fun _ _ => [])
    (fun _ _ _ => [])
    (fun _ => [])
    (fun _ _ _ _ => [])
    (fun _ _ _ _ => [])
    (fun _ => [])
    (fun _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ => [])
    (fun _ => [])
    (fun _ => [])
    (fun _ _ => [])
    (fun _ _ => [])
    (fun _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ => [])
    (fun _ _ => [])
    (fun _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ => [])
    (fun _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ _ => [])
    (fun _ => [])
    (fun _ _ => [])
    (fun _ _ => [])
    (fun _ => [])
    (fun _ => [])
    (fun _ _ => [])
    (fun _ _ => [])
    (fun _ _ => [])
    (fun _ _ _ _ => [])
    (fun _ => [])
    (fun _ => [])
    (fun _ => [])
    (fun _ _ _ => [])
    (fun _ _ _ _ => [])
    (fun _ _ => [])
    (fun _ _ => [])
    ([])
    ([])
    (fun _ _ _ _ _ => [])
    (fun _ => [])
    (fun _ _ _ _ => [])
    (fun _ => [])
    (fun _ _ => [])
    (fun _ _ => [])
    (fun _ _ _ => [])
    (fun _ => [])
    (fun _ => [])
    (fun _ => [])
    (fun _ => [])
    (fun _ _ _ => [])
    (fun _ _ _ => [])
    (fun _ => [])
    (fun _ _ => [])
    (fun _ _ _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ => [])
    ([])
    ([])
    ([])
    (fun _ _ _ _ => [])
    (fun _ _ => [])
    (fun _ _ => [])
    (fun _ => [])

theorem DirectConstness.mem_fields {c : Cat} {s : Syn c} {qualifier : Constness}
    (field : DirectConstness s qualifier) : qualifier ∈ constnessFieldsAt s := by
  cases field <;> exact List.mem_singleton_self _

theorem constnessFieldsAt_sound {c : Cat} (s : Syn c) (qualifier : Constness)
    (present : qualifier ∈ constnessFieldsAt s) : DirectConstness s qualifier := by
  cases s with
  | stateVar ty vis option override transient name init =>
    cases option with
    | none => exact False.elim (List.not_mem_nil present)
    | some value =>
      have same := List.mem_singleton.mp present
      cases same
      exact .stateVar ty vis override transient name init _
  | constant ty name value =>
    have same := List.mem_singleton.mp present
    cases same
    exact .constant ty name value
  | _ => exact False.elim (List.not_mem_nil present)

theorem constnessFieldsAt_iff {c : Cat} (s : Syn c) (qualifier : Constness) :
    qualifier ∈ constnessFieldsAt s ↔ DirectConstness s qualifier :=
  ⟨constnessFieldsAt_sound s qualifier,DirectConstness.mem_fields⟩

def constnessFeature : Constness → Feature
  | .constant => .constants
  | .immutable => .immutables

def constnessFeaturesAt {c : Cat} (s : Syn c) : List Feature :=
  (constnessFieldsAt s).map constnessFeature

theorem constnessFeaturesAt_iff {c : Cat} (s : Syn c) (f : Feature) :
    f ∈ constnessFeaturesAt s ↔
      ∃ qualifier, DirectConstness s qualifier ∧ constnessFeature qualifier = f := by
  change f ∈ (constnessFieldsAt s).map constnessFeature ↔ _
  rw [List.mem_map]
  constructor
  · rintro ⟨qualifier,present,same⟩
    exact ⟨qualifier,(constnessFieldsAt_iff s qualifier).mp present,same⟩
  · rintro ⟨qualifier,field,same⟩
    exact ⟨qualifier,(constnessFieldsAt_iff s qualifier).mpr field,same⟩

def syntaxConstnessUses {c : Cat} (root : Syn c) : List (SyntaxOccurrence × Constness) :=
  syntaxFieldUses root constnessFieldsAt

theorem syntaxConstnessUses_iff {c : Cat} (root : Syn c) (site : SyntaxOccurrence) (qualifier : Constness) :
    (site,qualifier) ∈ syntaxConstnessUses root ↔
      Syn.Sub site ⟨c,root⟩ ∧ DirectConstness site.2 qualifier := by
  rw [syntaxConstnessUses, syntaxFieldUses_iff, constnessFieldsAt_iff]

def declarationConstnessUses (E : Env) : List (DeclarationOccurrence × Constness) :=
  declarationFieldUses E constnessFieldsAt

theorem declarationConstnessUses_iff (E : Env) (site : DeclarationOccurrence) (qualifier : Constness) :
    (site,qualifier) ∈ declarationConstnessUses E ↔
      site.Occurs E ∧ DirectConstness site.2.2 qualifier := by
  rw [declarationConstnessUses, declarationFieldUses_iff, constnessFieldsAt_iff]

/-- info: 'Solidity.Frontend.Admission.constnessFieldsAt_iff' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms constnessFieldsAt_iff
/-- info: 'Solidity.Frontend.Admission.constnessFeaturesAt_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms constnessFeaturesAt_iff
/-- info: 'Solidity.Frontend.Admission.syntaxConstnessUses_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms syntaxConstnessUses_iff
/-- info: 'Solidity.Frontend.Admission.declarationConstnessUses_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms declarationConstnessUses_iff


theorem syntaxConstnessFeatures_eq {c : Cat} (root : Syn c) :
    syntaxFieldUses root constnessFeaturesAt =
      (syntaxConstnessUses root).map (fun use => (use.1,constnessFeature use.2)) :=
  syntaxFieldUses_map root constnessFieldsAt constnessFeature

theorem syntaxConstnessRefusals_eq {c : Cat} (root : Syn c) (accepts : Feature → Bool) :
    syntaxFieldRefusals root constnessFeaturesAt accepts =
      (syntaxFieldRefusals root constnessFieldsAt (fun value => accepts (constnessFeature value))).map
        (fun use => (use.1,constnessFeature use.2)) :=
  syntaxFieldRefusals_map root constnessFieldsAt constnessFeature accepts

/-- info: 'Solidity.Frontend.Admission.syntaxConstnessFeatures_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms syntaxConstnessFeatures_eq
/-- info: 'Solidity.Frontend.Admission.syntaxConstnessRefusals_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms syntaxConstnessRefusals_eq


/-! Regression: explicit override keywords (including some []) and true transient flags must survive syntax scanning. These markers certify no override resolution, storage legality, inferred qualifier or admission. -/
inductive DirectDeclarationQualifier : {c : Cat} → Syn c → Feature → Prop where
  | function {t : Bool} (name params vis mutability mods virtual returns body) (bases : List IdPath) :
      DirectDeclarationQualifier (.function (t := t) name params vis mutability mods virtual
        (some bases) returns body) .overrideDeclarations
  | modifier (name params virtual body) (bases : List IdPath) :
      DirectDeclarationQualifier (.modifier name params virtual (some bases) body) .overrideDeclarations
  | fallback (sig external mutability mods virtual body) (bases : List IdPath) :
      DirectDeclarationQualifier (.fallback sig external mutability mods virtual (some bases) body)
        .overrideDeclarations
  | receive (external payable mods virtual body) (bases : List IdPath) :
      DirectDeclarationQualifier (.receive external payable mods virtual (some bases) body)
        .overrideDeclarations
  | stateOverride (ty vis const transient name init) (bases : List IdPath) :
      DirectDeclarationQualifier (.stateVar ty vis const (some bases) transient name init)
        .overrideDeclarations
  | transient (ty vis const bases name init) :
      DirectDeclarationQualifier (.stateVar ty vis const bases true name init) .transientState

def overrideFeatures (bases : Option (List IdPath)) : List Feature :=
  bases.toList.map (fun _ => .overrideDeclarations)

def declarationQualifierFeaturesAt {c : Cat} (s : Syn c) : List Feature :=
  Syn.casesOn (motive := fun _ _ => List Feature) s
    ([])
    (fun _ _ => [])
    ([])
    (fun _ => [])
    (fun _ => [])
    (fun _ => [])
    (fun _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ => [])
    (fun _ _ => [])
    (fun _ _ _ _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ => [])
    (fun _ => [])
    (fun _ _ => [])
    (fun _ _ _ _ _ => [])
    (fun _ _ _ _ _ _ bases _ _ => overrideFeatures bases)
    (fun _ _ _ bases _ => overrideFeatures bases)
    (fun _ _ _ _ _ bases _ => overrideFeatures bases)
    ([])
    (fun _ _ _ => [])
    (fun _ _ _ _ bases _ => overrideFeatures bases)
    (fun _ _ _ => [])
    (fun _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ => [])
    (fun _ _ _ bases transient _ _ => overrideFeatures bases ++ (if transient then [.transientState] else []))
    (fun _ _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ => [])
    (fun _ _ => [])
    (fun _ => [])
    (fun _ _ _ => [])
    (fun _ _ _ _ => [])
    (fun _ _ => [])
    (fun _ => [])
    (fun _ => [])
    (fun _ _ => [])
    (fun _ _ => [])
    (fun _ _ _ => [])
    (fun _ => [])
    (fun _ _ _ _ => [])
    (fun _ _ _ _ => [])
    (fun _ => [])
    (fun _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ => [])
    (fun _ => [])
    (fun _ => [])
    (fun _ _ => [])
    (fun _ _ => [])
    (fun _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ => [])
    (fun _ _ => [])
    (fun _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ => [])
    (fun _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ _ => [])
    (fun _ => [])
    (fun _ _ => [])
    (fun _ _ => [])
    (fun _ => [])
    (fun _ => [])
    (fun _ _ => [])
    (fun _ _ => [])
    (fun _ _ => [])
    (fun _ _ _ _ => [])
    (fun _ => [])
    (fun _ => [])
    (fun _ => [])
    (fun _ _ _ => [])
    (fun _ _ _ _ => [])
    (fun _ _ => [])
    (fun _ _ => [])
    ([])
    ([])
    (fun _ _ _ _ _ => [])
    (fun _ => [])
    (fun _ _ _ _ => [])
    (fun _ => [])
    (fun _ _ => [])
    (fun _ _ => [])
    (fun _ _ _ => [])
    (fun _ => [])
    (fun _ => [])
    (fun _ => [])
    (fun _ => [])
    (fun _ _ _ => [])
    (fun _ _ _ => [])
    (fun _ => [])
    (fun _ _ => [])
    (fun _ _ _ _ => [])
    (fun _ _ _ => [])
    (fun _ _ => [])
    ([])
    ([])
    ([])
    (fun _ _ _ _ => [])
    (fun _ _ => [])
    (fun _ _ => [])
    (fun _ => [])

theorem DirectDeclarationQualifier.mem_features {c : Cat} {s : Syn c} {f : Feature}
    (field : DirectDeclarationQualifier s f) : f ∈ declarationQualifierFeaturesAt s := by
  cases field <;> simp [declarationQualifierFeaturesAt, overrideFeatures]

theorem declarationQualifierFeaturesAt_sound {c : Cat} (s : Syn c) (f : Feature)
    (present : f ∈ declarationQualifierFeaturesAt s) : DirectDeclarationQualifier s f := by
  cases s with
  | function name params vis mutability mods virtual bases returns body =>
    cases bases with
    | none => exact False.elim (List.not_mem_nil present)
    | some paths =>
      have same := List.mem_singleton.mp present
      cases same
      exact .function name params vis mutability mods virtual returns body paths
  | modifier name params virtual bases body =>
    cases bases with
    | none => exact False.elim (List.not_mem_nil present)
    | some paths =>
      have same := List.mem_singleton.mp present
      cases same
      exact .modifier name params virtual body paths
  | fallback sig external mutability mods virtual bases body =>
    cases bases with
    | none => exact False.elim (List.not_mem_nil present)
    | some paths =>
      have same := List.mem_singleton.mp present
      cases same
      exact .fallback sig external mutability mods virtual body paths
  | receive external payable mods virtual bases body =>
    cases bases with
    | none => exact False.elim (List.not_mem_nil present)
    | some paths =>
      have same := List.mem_singleton.mp present
      cases same
      exact .receive external payable mods virtual body paths
  | stateVar ty vis const bases transient name init =>
    change f ∈ overrideFeatures bases ++ (if transient then [.transientState] else []) at present
    rcases List.mem_append.mp present with overridden | isTransient
    · cases bases with
      | none => exact False.elim (List.not_mem_nil overridden)
      | some paths =>
        have same := List.mem_singleton.mp overridden
        cases same
        exact .stateOverride ty vis const transient name init paths
    · cases transient with
      | false => exact False.elim (List.not_mem_nil isTransient)
      | true =>
        have same := List.mem_singleton.mp isTransient
        cases same
        exact .transient ty vis const bases name init
  | _ => exact False.elim (List.not_mem_nil present)

theorem declarationQualifierFeaturesAt_iff {c : Cat} (s : Syn c) (f : Feature) :
    f ∈ declarationQualifierFeaturesAt s ↔ DirectDeclarationQualifier s f :=
  ⟨declarationQualifierFeaturesAt_sound s f,DirectDeclarationQualifier.mem_features⟩

def syntaxDeclarationQualifierUses {c : Cat} (root : Syn c) : List (SyntaxOccurrence × Feature) :=
  syntaxFieldUses root declarationQualifierFeaturesAt

theorem syntaxDeclarationQualifierUses_iff {c : Cat} (root : Syn c)
    (site : SyntaxOccurrence) (f : Feature) :
    (site,f) ∈ syntaxDeclarationQualifierUses root ↔
      Syn.Sub site ⟨c,root⟩ ∧ DirectDeclarationQualifier site.2 f := by
  rw [syntaxDeclarationQualifierUses, syntaxFieldUses_iff, declarationQualifierFeaturesAt_iff]

theorem syntaxDeclarationQualifierRefusals_iff {c : Cat} (root : Syn c)
    (accepts : Feature → Bool) (site : SyntaxOccurrence) (f : Feature) :
    (site,f) ∈ syntaxFieldRefusals root declarationQualifierFeaturesAt accepts ↔
      Syn.Sub site ⟨c,root⟩ ∧ DirectDeclarationQualifier site.2 f ∧ accepts f = false := by
  rw [syntaxFieldRefusals_iff, declarationQualifierFeaturesAt_iff]

/-- info: 'Solidity.Frontend.Admission.declarationQualifierFeaturesAt_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms declarationQualifierFeaturesAt_iff
/-- info: 'Solidity.Frontend.Admission.syntaxDeclarationQualifierUses_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms syntaxDeclarationQualifierUses_iff
/-- info: 'Solidity.Frontend.Admission.syntaxDeclarationQualifierRefusals_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms syntaxDeclarationQualifierRefusals_iff


/-! Regression: a top-level function needs its dedicated freeFunctions marker as well as generic function detection. Reuse the existing constructor projection and intrinsic declaration category; no indexed match, representation rewrite, typing or admission claim is introduced. -/
inductive DirectFreeFunction : {c : Cat} → Syn c → Prop where
  | function (name params vis mutability mods virtual bases returns body) :
      DirectFreeFunction (.function (t := true) name params vis mutability mods virtual bases returns body)

def freeFunctionFeaturesAt {c : Cat} (s : Syn c) : List Feature :=
  if c = .part true ∧ s.ctor = .function then [.freeFunctions] else []

theorem DirectFreeFunction.tags {c : Cat} {s : Syn c} (observed : DirectFreeFunction s) :
    c = .part true ∧ s.ctor = .function := by
  cases observed
  exact ⟨rfl,rfl⟩

theorem directFreeFunction_of_tags {c : Cat} (s : Syn c)
    (kind : c = .part true) (tag : s.ctor = .function) : DirectFreeFunction s := by
  cases s with
  | @function t name params vis mutability mods virtual bases returns body =>
    cases t with
    | false => cases kind
    | true => exact .function name params vis mutability mods virtual bases returns body
  | _ => cases tag

theorem freeFunctionFeaturesAt_iff {c : Cat} (s : Syn c) (f : Feature) :
    f ∈ freeFunctionFeaturesAt s ↔ f = .freeFunctions ∧ DirectFreeFunction s := by
  unfold freeFunctionFeaturesAt
  by_cases labels : c = .part true ∧ s.ctor = .function
  · rw [if_pos labels]
    exact ⟨fun present => ⟨List.mem_singleton.mp present,
      directFreeFunction_of_tags s labels.1 labels.2⟩,
      fun observed => List.mem_singleton.mpr observed.1⟩
  · rw [if_neg labels]
    exact ⟨fun impossible => False.elim (List.not_mem_nil impossible),
      fun observed => False.elim (labels observed.2.tags)⟩

def syntaxFreeFunctionUses {c : Cat} (root : Syn c) : List (SyntaxOccurrence × Feature) :=
  syntaxFieldUses root freeFunctionFeaturesAt

theorem syntaxFreeFunctionUses_iff {c : Cat} (root : Syn c) (site : SyntaxOccurrence) (f : Feature) :
    (site,f) ∈ syntaxFreeFunctionUses root ↔
      Syn.Sub site ⟨c,root⟩ ∧ f = .freeFunctions ∧ DirectFreeFunction site.2 := by
  rw [syntaxFreeFunctionUses, syntaxFieldUses_iff, freeFunctionFeaturesAt_iff]

/-- info: 'Solidity.Frontend.Admission.freeFunctionFeaturesAt_iff' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms freeFunctionFeaturesAt_iff
/-- info: 'Solidity.Frontend.Admission.syntaxFreeFunctionUses_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms syntaxFreeFunctionUses_iff


/-! Regression: unit-level pragma traversal must not duplicate markers at ancestor sites or erase raw words with the resolution environment. Reuse the existing intrinsic eliminator and generic visitor; tags assert neither lexical/version validity, coder selection, profile activation nor admission. -/
inductive DirectPragma : {c : Cat} → Syn c → List String → Prop where
  | pragma (words : List String) : DirectPragma (.pragma words) words

def pragmaWordsAt {c : Cat} (s : Syn c) : List (List String) := by
  apply Syn.casesOn (motive := fun _ _ => List (List String)) s
  case pragma => intro words; exact [words]
  all_goals (intros; exact [])

def pragmaFeature : List String → Feature
  | "solidity" :: _ => .pragmaVersion
  | ["abicoder", "v1"] | ["abicoder", "v2"] | ["experimental", "ABIEncoderV2"] => .pragmaAbicoder
  | _ => .pragmaOther

theorem pragmaWordsAt_iff {c : Cat} (s : Syn c) (words : List String) :
    words ∈ pragmaWordsAt s ↔ DirectPragma s words := by
  cases s with
  | pragma actual =>
    simp only [pragmaWordsAt, List.mem_singleton]
    constructor
    · intro same; cases same; exact .pragma _
    · intro direct; cases direct; rfl
  | _ =>
    simp only [pragmaWordsAt, List.not_mem_nil]
    constructor <;> intro impossible <;> cases impossible

def syntaxPragmaUses {c : Cat} (root : Syn c) : List (SyntaxOccurrence × Feature) :=
  syntaxFieldUses root (fun s => (pragmaWordsAt s).map pragmaFeature)

theorem syntaxPragmaUses_iff {c : Cat} (root : Syn c) (site : SyntaxOccurrence) (f : Feature) :
    (site,f) ∈ syntaxPragmaUses root ↔
      Syn.Sub site ⟨c,root⟩ ∧ ∃ words, DirectPragma site.2 words ∧ pragmaFeature words = f := by
  rw [syntaxPragmaUses, syntaxFieldUses_iff]
  constructor
  · rintro ⟨subterm,present⟩
    obtain ⟨words,present,same⟩ := List.mem_map.mp present
    exact ⟨subterm,words,(pragmaWordsAt_iff _ _).mp present,same⟩
  · rintro ⟨subterm,words,direct,same⟩
    exact ⟨subterm,List.mem_map.mpr ⟨words,(pragmaWordsAt_iff _ _).mpr direct,same⟩⟩

/-- info: 'Solidity.Frontend.Admission.pragmaWordsAt_iff' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms pragmaWordsAt_iff
/-- info: 'Solidity.Frontend.Admission.syntaxPragmaUses_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms syntaxPragmaUses_iff


/-! Regression: written array dimensions and nested unused types must survive extraction without inferring constant/positive bounds or validity. Reuse the intrinsic eliminator, constructor tag and generic visitor; old candidates and Source remain unchanged, with no profile/admission claim. -/
inductive DirectArrayType : {c : Cat} → Syn c → Feature → Prop where
  | dynamic (element : Syn .typeName) : DirectArrayType (.array element .none) .dynamicArrays
  | fixed (element : Syn .typeName) (length : Syn .expr) :
      DirectArrayType (.array element (.some length)) .fixedArrays

def arrayTypeFeaturesAt {c : Cat} (s : Syn c) : List Feature := by
  apply Syn.casesOn (motive := fun _ _ => List Feature) s
  case array =>
    intro element dimension
    exact [if dimension.ctor = .none then .dynamicArrays else .fixedArrays]
  all_goals (intros; exact [])

theorem arrayTypeFeaturesAt_iff {c : Cat} (s : Syn c) (f : Feature) :
    f ∈ arrayTypeFeaturesAt s ↔ DirectArrayType s f := by
  cases s with
  | array element dimension =>
    cases dimension with
    | none =>
      simp only [arrayTypeFeaturesAt, Syn.ctor, if_true, List.mem_singleton]
      constructor
      · intro same; cases same; exact .dynamic _
      · intro direct; cases direct; rfl
    | some length =>
      simp only [arrayTypeFeaturesAt, Syn.ctor, reduceCtorEq, if_false, List.mem_singleton]
      constructor
      · intro same; cases same; exact .fixed _ _
      · intro direct; cases direct; rfl
  | _ =>
    simp only [arrayTypeFeaturesAt, List.not_mem_nil]
    constructor <;> intro impossible <;> cases impossible

def syntaxArrayTypeUses {c : Cat} (root : Syn c) : List (SyntaxOccurrence × Feature) :=
  syntaxFieldUses root arrayTypeFeaturesAt

theorem syntaxArrayTypeUses_iff {c : Cat} (root : Syn c) (site : SyntaxOccurrence) (f : Feature) :
    (site,f) ∈ syntaxArrayTypeUses root ↔
      Syn.Sub site ⟨c,root⟩ ∧ DirectArrayType site.2 f := by
  rw [syntaxArrayTypeUses, syntaxFieldUses_iff, arrayTypeFeaturesAt_iff]

/-- info: 'Solidity.Frontend.Admission.arrayTypeFeaturesAt_iff' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms arrayTypeFeaturesAt_iff
/-- info: 'Solidity.Frontend.Admission.syntaxArrayTypeUses_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms syntaxArrayTypeUses_iff


/-! Regression: a visibility field on a function declaration must not become a function-type marker. Reuse the existing direct visibility projection and constructor tag; only written internal/external type visibility is classified, without inferring omitted defaults, validating signatures or changing policy/admission. -/
inductive DirectExplicitFunctionType : {c : Cat} → Syn c → Feature → Prop where
  | internal (params mutability returns) :
      DirectExplicitFunctionType (.fnType params (some .internal) mutability returns) .internalFunctionTypes
  | external (params mutability returns) :
      DirectExplicitFunctionType (.fnType params (some .external) mutability returns) .externalFunctionTypes

def functionTypeVisibilityFeature? : Visibility → Option Feature
  | .internal => some .internalFunctionTypes
  | .external => some .externalFunctionTypes
  | .priv | .pub => none

def explicitFunctionTypeFeaturesAt {c : Cat} (s : Syn c) : List Feature :=
  if s.ctor = .fnType then (visibilityFieldsAt s).filterMap functionTypeVisibilityFeature? else []

theorem explicitFunctionTypeFeaturesAt_iff {c : Cat} (s : Syn c) (f : Feature) :
    f ∈ explicitFunctionTypeFeaturesAt s ↔ DirectExplicitFunctionType s f := by
  cases s with
  | fnType params visibility mutability returns =>
    cases visibility with
    | none =>
      change f ∈ ([] : List Feature) ↔ _
      constructor <;> intro impossible <;> cases impossible
    | some value =>
      cases value with
      | internal =>
        change f ∈ [Feature.internalFunctionTypes] ↔ _
        constructor
        · intro same; cases List.mem_singleton.mp same; exact .internal _ _ _
        · intro direct; cases direct; exact List.mem_singleton.mpr rfl
      | external =>
        change f ∈ [Feature.externalFunctionTypes] ↔ _
        constructor
        · intro same; cases List.mem_singleton.mp same; exact .external _ _ _
        · intro direct; cases direct; exact List.mem_singleton.mpr rfl
      | priv =>
        change f ∈ ([] : List Feature) ↔ _
        constructor <;> intro impossible <;> cases impossible
      | pub =>
        change f ∈ ([] : List Feature) ↔ _
        constructor <;> intro impossible <;> cases impossible
  | _ =>
    simp only [explicitFunctionTypeFeaturesAt, Syn.ctor, reduceCtorEq, if_false, List.not_mem_nil]
    constructor <;> intro impossible <;> cases impossible

def syntaxExplicitFunctionTypeUses {c : Cat} (root : Syn c) : List (SyntaxOccurrence × Feature) :=
  syntaxFieldUses root explicitFunctionTypeFeaturesAt

theorem syntaxExplicitFunctionTypeUses_iff {c : Cat} (root : Syn c)
    (site : SyntaxOccurrence) (f : Feature) :
    (site,f) ∈ syntaxExplicitFunctionTypeUses root ↔
      Syn.Sub site ⟨c,root⟩ ∧ DirectExplicitFunctionType site.2 f := by
  rw [syntaxExplicitFunctionTypeUses, syntaxFieldUses_iff, explicitFunctionTypeFeaturesAt_iff]

/-- info: 'Solidity.Frontend.Admission.explicitFunctionTypeFeaturesAt_iff' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms explicitFunctionTypeFeaturesAt_iff
/-- info: 'Solidity.Frontend.Admission.syntaxExplicitFunctionTypeUses_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms syntaxExplicitFunctionTypeUses_iff


/-! Regression: grouping and tuple slots share a constructor but must not share a marker. Reuse intrinsic tags/elimination and the generic visitor; raw empty/holed forms retain syntax evidence, not typing, tuple-value, capture/evaluation-order, profile or admission guarantees. -/
inductive DirectTupleShape : {c : Cat} → Syn c → Feature → Prop where
  | group (value : Syn .expr) : DirectTupleShape (.tuple (.some value) .nil) .parentheses
  | empty : DirectTupleShape (.tuple .none .nil) .tupleExpressions
  | multiple (first next : Syn (.opt .expr)) (rest : Syn (.list (.opt .expr))) :
      DirectTupleShape (.tuple first (.cons next rest)) .tupleExpressions

def tupleShapeFeature (first : Syn (.opt .expr)) (rest : Syn (.list (.opt .expr))) : Feature :=
  if rest.ctor = .nil ∧ first.ctor = .some then .parentheses else .tupleExpressions

def tupleShapeFeaturesAt {c : Cat} (s : Syn c) : List Feature := by
  apply Syn.casesOn (motive := fun _ _ => List Feature) s
  case tuple => intro first rest; exact [tupleShapeFeature first rest]
  all_goals (intros; exact [])

theorem tupleShapeFeaturesAt_iff {c : Cat} (s : Syn c) (f : Feature) :
    f ∈ tupleShapeFeaturesAt s ↔ DirectTupleShape s f := by
  cases s with
  | tuple first rest =>
    cases rest with
    | nil =>
      cases first with
      | none =>
        change f ∈ [Feature.tupleExpressions] ↔ _
        constructor
        · intro same; cases List.mem_singleton.mp same; exact .empty
        · intro direct; cases direct; exact List.mem_singleton.mpr rfl
      | some value =>
        change f ∈ [Feature.parentheses] ↔ _
        constructor
        · intro same; cases List.mem_singleton.mp same; exact .group _
        · intro direct; cases direct; exact List.mem_singleton.mpr rfl
    | cons next tail =>
      change f ∈ [Feature.tupleExpressions] ↔ _
      constructor
      · intro same; cases List.mem_singleton.mp same; exact .multiple _ _ _
      · intro direct; cases direct; exact List.mem_singleton.mpr rfl
  | _ =>
    simp only [tupleShapeFeaturesAt, List.not_mem_nil]
    constructor <;> intro impossible <;> cases impossible

def syntaxTupleShapeUses {c : Cat} (root : Syn c) : List (SyntaxOccurrence × Feature) :=
  syntaxFieldUses root tupleShapeFeaturesAt

theorem syntaxTupleShapeUses_iff {c : Cat} (root : Syn c) (site : SyntaxOccurrence) (f : Feature) :
    (site,f) ∈ syntaxTupleShapeUses root ↔
      Syn.Sub site ⟨c,root⟩ ∧ DirectTupleShape site.2 f := by
  rw [syntaxTupleShapeUses, syntaxFieldUses_iff, tupleShapeFeaturesAt_iff]

/-- info: 'Solidity.Frontend.Admission.tupleShapeFeaturesAt_iff' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms tupleShapeFeaturesAt_iff
/-- info: 'Solidity.Frontend.Admission.syntaxTupleShapeUses_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms syntaxTupleShapeUses_iff


/-! Regression: only explicit array/bytes/string creation targets identify memory syntax; unresolved names and elementary metadata on other constructors must not masquerade as memory creation. This is head syntax, not allocation, typing, panic, profile or admission evidence. -/
inductive DirectMemoryCreationHead : {c : Cat} → Syn c → Prop where
  | array (element : Syn .typeName) (dimension : Syn (.opt .expr)) :
      DirectMemoryCreationHead (.new (.array element dimension))
  | bytes : DirectMemoryCreationHead (.new (.elem .bytes))
  | string : DirectMemoryCreationHead (.new (.elem .string))

def memoryCreationTarget (target : Syn .typeName) : Bool := by
  apply Syn.casesOn (motive := fun _ _ => Bool) target
  case array => intros; exact true
  case elem => intro e; exact e == .bytes || e == .string
  all_goals (intros; exact false)

def memoryCreationHeadFeaturesAt {c : Cat} (s : Syn c) : List Feature := by
  apply Syn.casesOn (motive := fun _ _ => List Feature) s
  case new => intro target; exact if memoryCreationTarget target then [.newMemory] else []
  all_goals (intros; exact [])

theorem memoryCreationHeadFeaturesAt_iff {c : Cat} (s : Syn c) (f : Feature) :
    f ∈ memoryCreationHeadFeaturesAt s ↔ DirectMemoryCreationHead s ∧ f = .newMemory := by
  cases s with
  | new target =>
    cases target with
    | array element dimension =>
      change f ∈ [Feature.newMemory] ↔ _
      exact ⟨fun h => ⟨.array _ _,List.mem_singleton.mp h⟩,
        fun h => List.mem_singleton.mpr h.2⟩
    | elem e =>
      cases e
      all_goals first
        | (change f ∈ [Feature.newMemory] ↔ _
           constructor
           · intro h; exact ⟨.bytes,List.mem_singleton.mp h⟩
           · intro h; exact List.mem_singleton.mpr h.2)
        | (change f ∈ [Feature.newMemory] ↔ _
           constructor
           · intro h; exact ⟨.string,List.mem_singleton.mp h⟩
           · intro h; exact List.mem_singleton.mpr h.2)
        | (change f ∈ ([] : List Feature) ↔ _
           constructor
           · intro h; cases h
           · intro h; cases h.1)
    | _ =>
      simp only [memoryCreationHeadFeaturesAt, memoryCreationTarget, Bool.false_eq_true,
        ↓reduceIte, List.not_mem_nil, false_iff]
      intro h; cases h.1
  | _ =>
    simp only [memoryCreationHeadFeaturesAt, List.not_mem_nil, false_iff]
    intro h; cases h.1

theorem syntaxMemoryCreationHeadUses_iff {c : Cat} (root : Syn c)
    (site : SyntaxOccurrence) (f : Feature) :
    (site,f) ∈ syntaxFieldUses root memoryCreationHeadFeaturesAt ↔
      Syn.Sub site ⟨c,root⟩ ∧ DirectMemoryCreationHead site.2 ∧ f = .newMemory := by
  rw [syntaxFieldUses_iff, memoryCreationHeadFeaturesAt_iff]

/-- info: 'Solidity.Frontend.Admission.memoryCreationHeadFeaturesAt_iff' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms memoryCreationHeadFeaturesAt_iff
/-- info: 'Solidity.Frontend.Admission.syntaxMemoryCreationHeadUses_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms syntaxMemoryCreationHeadUses_iff

end Solidity.Frontend.Admission
