import Solidity.Frontend.Admission.DeclarationOccurrences
import Solidity.Language.Features

/-!
# Elementary-type features at actual Source syntax sites

Regression: mapping keys and value-type underlying types carry `Elem` fields,
not separate `Syn` children. A declaration-wide feature inventory must retain
these fields as well as elementary type names and elementary conversion heads.
This collector reuses the canonical declaration visitor. It classifies only
these explicit elementary fields; resolved user types, lexical features, the
remaining feature inventory and admission remain separate obligations.
-/
namespace Solidity.Frontend.Admission
open Solidity.Source Solidity.Language

/-- One catalog feature for an intrinsic elementary type, without parsing names. -/
def elementaryFeature : Elem → Feature
  | .address | .addressPayable => .addressTypes
  | .bool => .boolType
  | .string => .stringType
  | .bytes => .dynamicBytesType
  | .int _ _ _ => .integerTypes
  | .fixedBytes _ _ => .fixedBytesTypes
  | .fixed _ _ => .fixedPoint

/-- Direct elementary fields only. Syntax descendants are visited by the
existing generic visitor, not recursively duplicated here. -/
def elementaryFieldsAt {c : Cat} (s : Syn c) : List Elem :=
  Syn.casesOn (motive := fun _ _ => List Elem) s
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
    (fun _ e => [e]) -- udvt
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
    (fun _ _ _ => []) -- param
    (fun e => [e]) -- elem
    (fun _ _ _ _ => []) -- fnType
    (fun key _ _ _ => match key with | .elem e _ => [e] | .path _ => []) -- mapping
    (fun _ => []) -- userType
    (fun _ _ => []) -- array
    (fun _ _ _ => []) -- varDecl
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
    (fun e _ => [e]) -- elemType
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

/-- The original declaration and syntax site accompany each field value. -/
def declarationElementaryUses (E : Env) : List (DeclarationOccurrence × Elem) :=
  (declarationOccurrences E).flatMap fun site =>
    (elementaryFieldsAt site.2.2).map fun e => (site,e)

/-- Exact occurrence membership: an actual carried declaration, an intrinsic
subterm, and one of that site's direct elementary fields. -/
theorem declarationElementaryUses_iff (E : Env)
    (site : DeclarationOccurrence) (e : Elem) :
    (site,e) ∈ declarationElementaryUses E ↔
      site.Occurs E ∧ e ∈ elementaryFieldsAt site.2.2 := by
  exact declarationFieldUses_iff E elementaryFieldsAt site e

/-- Mapping-key metadata is retained even though it is not a syntax child. -/
theorem mapping_key_field (e : Elem) (valid : e ≠ .addressPayable)
    (keyName : Option String) (value : Syn .typeName) (valueName : Option String) :
    elementaryFieldsAt (.mapping (.elem e valid) keyName value valueName) = [e] := rfl

/-- Value-type underlying metadata is retained without resolving its name. -/
theorem value_type_field {top : Bool} (name : String) (e : Elem) :
    elementaryFieldsAt (.udvt (t := top) name e) = [e] := rfl

/-- Fixed-point syntax is reported as fixed-point, without inferring that its
policy eligibility supplies an implementation. -/
theorem elementaryFeature_fixedPoint_iff (e : Elem) :
    elementaryFeature e = .fixedPoint ↔
      ∃ signed dims, e = .fixed signed dims := by
  cases e with
  | fixed signed dims =>
    exact ⟨fun _ => ⟨signed,dims,rfl⟩,fun _ => rfl⟩
  | _ => simp only [elementaryFeature, reduceCtorEq, exists_false]

/-- Ordered elementary-feature projection of the provenance-carrying uses.
Duplicates are retained; this is not the complete program feature list. -/
def declarationElementaryFeatures (E : Env) : List Feature :=
  (declarationElementaryUses E).map fun use => elementaryFeature use.2

/-- Every reported elementary feature has an actual declaration/site/field
witness, and every such field contributes its classified feature. -/
theorem declarationElementaryFeatures_iff (E : Env) (f : Feature) :
    f ∈ declarationElementaryFeatures E ↔
      ∃ (site : DeclarationOccurrence) (e : Elem), site.Occurs E ∧ e ∈ elementaryFieldsAt site.2.2 ∧
        elementaryFeature e = f := by
  simp only [declarationElementaryFeatures, List.mem_map]
  constructor
  · rintro ⟨⟨site,e⟩,member,equality⟩
    have present := (declarationElementaryUses_iff E site e).mp member
    exact ⟨site,e,present.1,present.2,equality⟩
  · rintro ⟨site,e,occurs,present,equality⟩
    exact ⟨(site,e),(declarationElementaryUses_iff E site e).mpr
      ⟨occurs,present⟩,equality⟩

/-- info: 'Solidity.Frontend.Admission.declarationElementaryUses_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms declarationElementaryUses_iff

/-- info: 'Solidity.Frontend.Admission.mapping_key_field' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms mapping_key_field

/-- info: 'Solidity.Frontend.Admission.value_type_field' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms value_type_field

/-- info: 'Solidity.Frontend.Admission.elementaryFeature_fixedPoint_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms elementaryFeature_fixedPoint_iff

/-- info: 'Solidity.Frontend.Admission.declarationElementaryFeatures_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms declarationElementaryFeatures_iff

/-- Every extracted elementary feature is witnessed by an actual syntax site
and direct elementary field in the original unit. This is one-way provenance,
not completeness of the whole feature catalog or a source admission proof. -/
theorem declarationElementaryFeatures_source_witness (u : Syn .unit) (f : Feature)
    (present : f ∈ declarationElementaryFeatures u.env) :
    ∃ (site : SyntaxOccurrence) (e : Elem), site ∈ syntaxOccurrences u ∧
      e ∈ elementaryFieldsAt site.2 ∧ elementaryFeature e = f := by
  obtain ⟨site,e,occurs,field,classified⟩ :=
    (declarationElementaryFeatures_iff u.env f).mp present
  refine ⟨site.2,e,?_,field,classified⟩
  exact declaration_occurrence_in_source_unit u site
    ((declarationOccurrences_iff u.env site).mpr occurs)

/-- info: 'Solidity.Frontend.Admission.declarationElementaryFeatures_source_witness' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms declarationElementaryFeatures_source_witness

end Solidity.Frontend.Admission
