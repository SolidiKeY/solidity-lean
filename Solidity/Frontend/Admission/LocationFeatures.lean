import Solidity.Frontend.Admission.DeclarationOccurrences
import Solidity.Language.Features

/-! # Explicit data-location metadata at declaration syntax sites

Regression: parameter and variable-declaration data locations are metadata, not `Syn` children. Catch parameters and unused declarations must retain their explicit memory/storage/calldata fields. This module classifies every direct `DataLoc` field in `Syn` through the shared declaration collector, with an independent two-constructor relation accounting for all direct field cases. Implicit or inferred locations, resolved types, full feature coverage and operational admission remain separate obligations. -/
namespace Solidity.Frontend.Admission
open Solidity.Source Solidity.Language

/-- The independent relation contains exactly the two syntax constructors whose metadata carries an explicit data location. -/
inductive DirectDataLocation : {c : Cat} → Syn c → DataLoc → Prop where
  | param (ty : Syn .typeName) (loc : DataLoc) (name : Option String) :
      DirectDataLocation (.param ty (some loc) name) loc
  | variable (ty : Syn .typeName) (loc : DataLoc) (name : String) :
      DirectDataLocation (.varDecl ty (some loc) name) loc

/-- Direct explicit fields only; the generic visitor handles descendants. The motive generalizes the category to avoid equation-compiler casts. -/
def dataLocationFieldsAt {c : Cat} (s : Syn c) : List DataLoc :=
  Syn.casesOn (motive := fun _ _ => List DataLoc) s
    ([]) -- nil
    (fun _ _ => []) -- cons
    ([]) -- none
    (fun _ => []) -- some
    (fun _ => []) -- unit
    (fun _ => []) -- pragma
    (fun _ _ => []) -- importPath
    (fun _ _ _ => []) -- importSymbols
    (fun _ _ => []) -- importStar
    (fun _ _ => []) -- importAlias
    (fun _ _ _ _ _ => []) -- contract
    (fun _ _ _ => []) -- interface
    (fun _ _ => []) -- library
    (fun _ => []) -- topPart
    (fun _ _ => []) -- inherit
    (fun _ _ _ _ _ => []) -- constructor
    (fun _ _ _ _ _ _ _ _ _ => []) -- function
    (fun _ _ _ _ _ => []) -- modifier
    (fun _ _ _ _ _ _ _ => []) -- fallback
    ([]) -- fbNoParams
    (fun _ _ _ => []) -- fbParams
    (fun _ _ _ _ _ _ => []) -- receive
    (fun _ _ _ => []) -- struct
    (fun _ _ => []) -- structMember
    (fun _ _ _ => []) -- enum
    (fun _ _ => []) -- udvt
    (fun _ _ _ _ _ _ _ => []) -- stateVar
    (fun _ _ _ => []) -- constant
    (fun _ _ _ => []) -- event
    (fun _ _ _ => []) -- eventParam
    (fun _ _ => []) -- error
    (fun _ _ => []) -- errorParam
    (fun _ => []) -- usingPart
    (fun _ _ _ => []) -- usingPath
    (fun _ _ _ _ => []) -- usingAliases
    (fun _ _ => []) -- usingAlias
    (fun _ => []) -- positional
    (fun _ => []) -- named
    (fun _ _ => []) -- namedArg
    (fun _ _ => []) -- modInv
    (fun _ loc _ => loc.toList) -- param
    (fun _ => []) -- elem
    (fun _ _ _ _ => []) -- fnType
    (fun _ _ _ _ => []) -- mapping
    (fun _ => []) -- userType
    (fun _ _ => []) -- array
    (fun _ loc _ => loc.toList) -- varDecl
    (fun _ _ => []) -- index
    (fun _ _ _ => []) -- slice
    (fun _ _ => []) -- member
    (fun _ _ _ => []) -- callOptions
    (fun _ _ => []) -- call
    (fun _ => []) -- payableConv
    (fun _ => []) -- metaType
    (fun _ _ => []) -- unaryPrefix
    (fun _ _ => []) -- unarySuffix
    (fun _ _ => []) -- exp
    (fun _ _ _ => []) -- mulDivMod
    (fun _ _ _ => []) -- addSub
    (fun _ _ _ => []) -- shift
    (fun _ _ => []) -- bitAnd
    (fun _ _ => []) -- bitXor
    (fun _ _ => []) -- bitOr
    (fun _ _ _ => []) -- order
    (fun _ _ _ => []) -- equality
    (fun _ _ => []) -- and
    (fun _ _ => []) -- or
    (fun _ _ _ => []) -- cond
    (fun _ _ _ => []) -- assign
    (fun _ => []) -- new
    (fun _ _ => []) -- tuple
    (fun _ _ => []) -- inlineArray
    (fun _ => []) -- ident
    (fun _ => []) -- lit
    (fun _ _ => []) -- litUnit
    (fun _ _ => []) -- elemType
    (fun _ _ => []) -- declVar
    (fun _ _ _ _ => []) -- declTuple
    (fun _ => []) -- exprStmt
    (fun _ => []) -- blockStmt
    (fun _ => []) -- simpleStmt
    (fun _ _ _ => []) -- ifStmt
    (fun _ _ _ _ => []) -- forStmt
    (fun _ _ => []) -- whileStmt
    (fun _ _ => []) -- doWhile
    ([]) -- continueStmt
    ([]) -- breakStmt
    (fun _ _ _ _ _ => []) -- tryStmt
    (fun _ => []) -- catchPlain
    (fun _ _ _ _ => []) -- catchSig
    (fun _ => []) -- returnStmt
    (fun _ _ => []) -- emit
    (fun _ _ => []) -- revert
    (fun _ _ _ => []) -- assembly
    (fun _ => []) -- block
    (fun _ => []) -- stmtItem
    (fun _ => []) -- uncheckedItem
    (fun _ => []) -- yulBlock
    (fun _ _ _ => []) -- yulLet
    (fun _ _ _ => []) -- yulAssign
    (fun _ => []) -- yulExprStmt
    (fun _ _ => []) -- yulIf
    (fun _ _ _ _ => []) -- yulFor
    (fun _ _ _ => []) -- yulSwitch
    (fun _ _ => []) -- yulCase
    ([]) -- yulLeave
    ([]) -- yulBreak
    ([]) -- yulContinue
    (fun _ _ _ _ => []) -- yulFun
    (fun _ _ => []) -- yulPath
    (fun _ _ => []) -- yulCall
    (fun _ => []) -- yulLit

/-- Every independently specified explicit field is collected. -/
theorem DirectDataLocation.mem_fields {c : Cat} {s : Syn c} {loc : DataLoc}
    (field : DirectDataLocation s loc) : loc ∈ dataLocationFieldsAt s := by
  cases field <;> exact List.mem_singleton_self _

/-- All syntax constructors are accounted for; only parameter and variable metadata with a present location can produce a collected field. -/
theorem dataLocationFieldsAt_sound {c : Cat} (s : Syn c) (loc : DataLoc)
    (present : loc ∈ dataLocationFieldsAt s) : DirectDataLocation s loc := by
  cases s with
  | param ty place name =>
    cases place with
    | none => exact False.elim (List.not_mem_nil present)
    | some value =>
      have same := List.mem_singleton.mp present
      cases same
      exact .param ty loc name
  | varDecl ty place name =>
    cases place with
    | none => exact False.elim (List.not_mem_nil present)
    | some value =>
      have same := List.mem_singleton.mp present
      cases same
      exact .variable ty loc name
  | _ => exact False.elim (List.not_mem_nil present)

/-- Exact direct-field membership against the independent relation. -/
theorem dataLocationFieldsAt_iff {c : Cat} (s : Syn c) (loc : DataLoc) :
    loc ∈ dataLocationFieldsAt s ↔ DirectDataLocation s loc :=
  ⟨dataLocationFieldsAt_sound s loc,DirectDataLocation.mem_fields⟩

/-- Literal location metadata maps to its catalog feature, without inferring an omitted location or resolving a user-defined type. -/
def dataLocationFeature : DataLoc → Feature
  | .memory => .memoryLocation
  | .storage => .storageLocation
  | .calldata => .calldataLocation

/-- Uses retain actual declarations/sites and explicit location values. -/
def declarationLocationUses (E : Env) : List (DeclarationOccurrence × DataLoc) :=
  declarationFieldUses E dataLocationFieldsAt

/-- Exact accounting includes unused bodies and nested catch parameters. -/
theorem declarationLocationUses_iff (E : Env) (site : DeclarationOccurrence)
    (loc : DataLoc) :
    (site,loc) ∈ declarationLocationUses E ↔
      site.Occurs E ∧ DirectDataLocation site.2.2 loc := by
  change (site,loc) ∈ declarationFieldUses E dataLocationFieldsAt ↔ _
  rw [declarationFieldUses_iff, dataLocationFieldsAt_iff]

/-- Ordered feature projection; duplicates and actual source sites are retained in the underlying uses. This is only the explicit-location feature subset. -/
def declarationLocationFeatures (E : Env) : List Feature :=
  (declarationLocationUses E).map fun use => dataLocationFeature use.2

/-- Each feature has an actual declaration/site/location witness, and each such explicit field contributes its feature. -/
theorem declarationLocationFeatures_iff (E : Env) (f : Feature) :
    f ∈ declarationLocationFeatures E ↔
      ∃ (site : DeclarationOccurrence) (loc : DataLoc),
        site.Occurs E ∧ DirectDataLocation site.2.2 loc ∧ dataLocationFeature loc = f := by
  simp only [declarationLocationFeatures, List.mem_map]
  constructor
  · rintro ⟨⟨site,loc⟩,present,equality⟩
    have found := (declarationLocationUses_iff E site loc).mp present
    exact ⟨site,loc,found.1,found.2,equality⟩
  · rintro ⟨site,loc,occurs,field,equality⟩
    exact ⟨(site,loc),(declarationLocationUses_iff E site loc).mpr
      ⟨occurs,field⟩,equality⟩

/-- A reported feature is tied to an original source-unit syntax site, rather than merely a supplied roster or a matching feature name. -/
theorem declarationLocationFeatures_source_witness (unit : Syn .unit) (f : Feature)
    (present : f ∈ declarationLocationFeatures unit.env) :
    ∃ (site : SyntaxOccurrence) (loc : DataLoc), site ∈ syntaxOccurrences unit ∧
      DirectDataLocation site.2 loc ∧ dataLocationFeature loc = f := by
  obtain ⟨site,loc,occurs,field,classified⟩ :=
    (declarationLocationFeatures_iff unit.env f).mp present
  exact ⟨site.2,loc,declaration_occurrence_in_source_unit unit site
    ((declarationOccurrences_iff unit.env site).mpr occurs),field,classified⟩

/-- Every explicit location in any carried declaration subterm contributes its feature; no execution-root or additional roster hypothesis is required. -/
theorem declaration_location_subterm_reported (E : Env) (d : Decl)
    (member : d ∈ E.decls) {c : Cat} (s : Syn c)
    (subterm : Syn.Sub ⟨c,s⟩ ⟨d.kind.cat d.top,d.node⟩)
    (loc : DataLoc) (field : DirectDataLocation s loc) :
    dataLocationFeature loc ∈ declarationLocationFeatures E :=
  (declarationLocationFeatures_iff E _).mpr
    ⟨(d,⟨c,s⟩),loc,⟨member,subterm⟩,field,rfl⟩

/-- Syntax-only unused function fixture guarding declaration-wide coverage and absent metadata. No Source typing or operational admission is asserted. -/
def explicitLocationUnit (place : Option DataLoc) : Syn .unit :=
  .unit (.cons (.topPart (.function (.ident "unused")
    (.cons (.param (.elem .bytes) place (some "payload")) .nil)
    none none .nil false none .nil .none)) .nil)

/-- One generic regression covers all three explicit locations and omission: unused syntax is retained, while no default location is invented for `none`. -/
theorem explicitLocationUnit_features (place : Option DataLoc) :
    declarationLocationFeatures (explicitLocationUnit place).env =
      place.toList.map dataLocationFeature := by
  cases place <;> rfl

/-- Positive declaration coverage is nonempty for every explicit location. -/
theorem unused_parameter_location_reported (loc : DataLoc) :
    dataLocationFeature loc ∈ declarationLocationFeatures (explicitLocationUnit (some loc)).env := by
  rw [explicitLocationUnit_features]
  exact List.mem_singleton_self _

/-- info: 'Solidity.Frontend.Admission.DirectDataLocation.mem_fields' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms DirectDataLocation.mem_fields
/-- info: 'Solidity.Frontend.Admission.dataLocationFieldsAt_sound' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms dataLocationFieldsAt_sound
/-- info: 'Solidity.Frontend.Admission.dataLocationFieldsAt_iff' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms dataLocationFieldsAt_iff
/-- info: 'Solidity.Frontend.Admission.declarationLocationUses_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms declarationLocationUses_iff
/-- info: 'Solidity.Frontend.Admission.declarationLocationFeatures_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms declarationLocationFeatures_iff
/-- info: 'Solidity.Frontend.Admission.declarationLocationFeatures_source_witness' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms declarationLocationFeatures_source_witness

/-- info: 'Solidity.Frontend.Admission.declaration_location_subterm_reported' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms declaration_location_subterm_reported
/-- info: 'Solidity.Frontend.Admission.explicitLocationUnit_features' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms explicitLocationUnit_features
/-- info: 'Solidity.Frontend.Admission.unused_parameter_location_reported' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms unused_parameter_location_reported

/-- Omitted location metadata cannot create an intrinsic refusal, for any supplied acceptance predicate. This does not infer a default location. -/
theorem omitted_location_no_refusal (accepts : DataLoc → Bool) :
    declarationFieldRefusal? (explicitLocationUnit none).env dataLocationFieldsAt accepts = none := rfl

/-- The same real unused syntax is silent under accept-all and non-silent under reject-all. The generic predicate is not itself an admission policy; this control must not be mistaken for operational eligibility. -/
theorem explicit_location_predicate_gap (loc : DataLoc) :
    declarationFieldRefusal? (explicitLocationUnit (some loc)).env dataLocationFieldsAt
      (fun _ => true) = none ∧
    declarationFieldRefusal? (explicitLocationUnit (some loc)).env dataLocationFieldsAt
      (fun _ => false) ≠ none := by
  constructor
  · exact (declarationFieldRefusal?_none_iff _ dataLocationFieldsAt (fun _ => true)).mpr
      (fun _ _ _ _ => rfl)
  · intro silent
    have accepted := (declarationFieldRefusal?_none_iff _ dataLocationFieldsAt
      (fun _ => false)).mp silent
    obtain ⟨site,value,occurs,field,_⟩ :=
      (declarationLocationFeatures_iff _ (dataLocationFeature loc)).mp
        (unused_parameter_location_reported loc)
    have impossible : false = true := accepted site value occurs field.mem_fields
    cases impossible

/-- info: 'Solidity.Frontend.Admission.omitted_location_no_refusal' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms omitted_location_no_refusal
/-- info: 'Solidity.Frontend.Admission.explicit_location_predicate_gap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms explicit_location_predicate_gap

end Solidity.Frontend.Admission
