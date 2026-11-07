import Solidity.Lowering.P8.SourceAstLiteralCorrespondence

/-! Parameter and array structural correspondence for existing readers.
Regression purpose: retain parameter qualifiers/names/order and array base /
bound syntax. Field and child-result hypotheses expose supported conversion,
not Source admission, compiler provenance or execution assumptions. -/
namespace Solidity.Lowering.P8.SourceAstParameterCorrespondence
open Lean Solidity.Source
open SourceAstParameters SourceAstCorrespondence SourceAstExpressionCorrespondence

/-- Exact parameter type, location and anonymous/named spelling are retained. -/
theorem parameter_exact (readType : Json → Except String (Syn .typeName))
    (node rawType : Json) (ty : Syn .typeName) (location name : String)
    (loc : Option DataLoc)
    (kind : node.getObjValAs? String "nodeType" = .ok "VariableDeclaration")
    (typeField : node.getObjVal? "typeName" = .ok rawType)
    (converted : readType rawType = .ok ty)
    (locationField : node.getObjValAs? String "storageLocation" = .ok location)
    (locationValue : SourceAstTypes.location location = .ok loc)
    (nameField : node.getObjValAs? String "name" = .ok name) :
    SourceAstCompoundTypes.parameterWith readType node =
      .ok (.param ty loc (if name.isEmpty then none else some name)) := by
  unfold SourceAstCompoundTypes.parameterWith
  simp only [kind, typeField, converted, locationField, locationValue, nameField,
    ok_bind, beq_self_eq_true, ite_true, pure_bind]
  rfl

/-- Exact ordered child accounting for recursive parameter containers. -/
theorem parameters_ok_iff_each (readType : Json → Except String (Syn .typeName))
    (node : Json) (children : Array Json) (out : Syn (.list .param))
    (kind : node.getObjValAs? String "nodeType" = .ok "ParameterList")
    (fields : node.getObjValAs? (Array Json) "parameters" = .ok children) :
    SourceAstCompoundTypes.parametersWith readType node = .ok out ↔
      ∃ values, Each (fun child value =>
        SourceAstCompoundTypes.parameterWith readType child = .ok value)
        children.toList values ∧ out = syntaxList values := by
  unfold SourceAstCompoundTypes.parametersWith
  simp only [kind, fields, ok_bind, beq_self_eq_true, ite_true, pure_bind]
  exact build_ok_iff_each (SourceAstCompoundTypes.parameterWith readType)
    (fun (values : List (Syn .param)) => (syntaxList values : Syn (.list .param)))
    children.toList out

/-- Both dynamic and fixed arrays keep their converted base and exact bound;
this reuses the same optional-expression reader as tuple correspondence. -/
theorem array_exact (fuel : Nat) (node rawBase rawBound : Json)
    (base : Syn .typeName) (bound : Syn (.opt .expr))
    (kind : node.getObjValAs? String "nodeType" = .ok "ArrayTypeName")
    (baseField : node.getObjVal? "baseType" = .ok rawBase)
    (baseValue : SourceAstCompoundTypes.typeName fuel rawBase = .ok base)
    (boundField : node.getObjVal? "length" = .ok rawBound)
    (boundValue : SourceAstStatements.optionalExpression fuel rawBound = .ok bound) :
    SourceAstCompoundTypes.typeName (fuel + 1) node = .ok (.array base bound) := by
  rw [SourceAstCompoundTypes.typeName]
  simp only [kind, baseField, baseValue, boundField, ok_bind]
  cases rawBound
  case null =>
    change Except.ok Syn.none = Except.ok bound at boundValue
    cases boundValue
    rfl
  all_goals
    simp only [SourceAstStatements.optionalExpression] at boundValue
    rw [boundValue]
    rfl

/-- info: 'Solidity.Lowering.P8.SourceAstParameterCorrespondence.parameter_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms parameter_exact
/-- info: 'Solidity.Lowering.P8.SourceAstParameterCorrespondence.parameters_ok_iff_each' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms parameters_ok_iff_each
/-- info: 'Solidity.Lowering.P8.SourceAstParameterCorrespondence.array_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms array_exact
end Solidity.Lowering.P8.SourceAstParameterCorrespondence
